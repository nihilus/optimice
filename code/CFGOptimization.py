'''
    Control Flow Graph optimization class
'''
import copy
import array
import re

import idc
import idautils
import idaapi

debug = 0


jcc_map = { 'jo':['jno'], 'jno':['jo'],
'jb':['jnb','jae', 'jnc'], 'jnae':['jnb','jae', 'jnc'], 'jc':['jnb','jae', 'jnc'], 'jnb':['jb','jnae','jc'], 'jae':['jb','jnae','jc'], 'jnc':['jb','jnae','jc'],
'jz':['jnz','jne'], 'je':['jnz','jne'], 'jnz':['jz', 'je'], 'jne':['jz', 'je'],
'jbe':['jnbe', 'ja'], 'jna':['jnbe', 'ja'], 'jnbe':['jbe', 'jna'], 'ja':['jbe', 'jna'],
'js':['jns'], 'jns':['js'],
'jp':['jnp','jpo'], 'jpe':['jnp','jpo'], 'jnp':['jp', 'jpe'], 'jpo':['jp', 'jpe'], 
'jl':['jnl', 'jge'], 'jnge':['jnl', 'jge'], 'jnl':['jl', 'jnge'], 'jge':['jl', 'jnge'], 
'jle':['jnle', 'jg'], 'jng':['jnle', 'jg'], 'jnle':['jle', 'jng'], 'jg':['jle', 'jng'] }

jcc_synonym = { 'jo':['jo'], 'jno':['jno'],
'jb':['jb','jnae','jc'], 'jnae':['jb','jnae','jc'], 'jc':['jb','jnae','jc'], 'jnb':['jnb','jae', 'jnc'], 'jae':['jnb','jae', 'jnc'], 'jnc':['jnb','jae', 'jnc'],
'jz':['jz', 'je'], 'je':['jz', 'je'], 'jnz':['jnz','jne'], 'jne':['jnz','jne'],
'jbe':['jbe', 'jna'], 'jna':['jbe', 'jna'], 'jnbe':['jnbe', 'ja'], 'ja':['jnbe', 'ja'],
'js':['js'], 'jns':['jns'],
'jp':['jp', 'jpe'], 'jpe':['jp', 'jpe'], 'jnp':['jnp','jpo'], 'jpo':['jnp','jpo'], 
'jl':['jl', 'jnge'], 'jnge':['jl', 'jnge'], 'jnl':['jnl', 'jge'], 'jge':['jnl', 'jge'], 
'jle':['jle', 'jng'], 'jng':['jle', 'jng'], 'jnle':['jnle', 'jg'], 'jg':['jnle', 'jg'] }

class MiscError(Exception):
    def __init__(self):
        return


class ReduceJMP:
    """Function CFG JMP reduction"""


    def __init__(self, function):
        self.function = function


    def Reduce(self, function=None):
        if function != None:
            self.function = function
        if self.function == None:
            raise MiscError
        
        modified = False
        changed = True
        while changed:
            changed = False

            for bb_ea in self.function.DFSFalseTraverseBlocks():
                #get last instruction from block (this is only place for branch
                #instruction)
                instr = self.function.GetBBLastInstruction(bb_ea)

                if instr.IsJmp():
                    if debug:
                        print ">ReduceJMP:Reduce1 - JMP@[%08x] BB[%08x] Mnem[%s]"  % (instr.GetOriginEA(), bb_ea, instr.GetMnem())
                        
                    refs_from = list(self.function.GetRefsFrom(instr.GetOriginEA()))
                    
                    if debug:
                        print ">ReduceJMP:Reduce - RefsFrom:", refs_from
                    
                    if len(refs_from) == 0 or refs_from[0][0] == None or len(refs_from) > 1:
                        #this is a case for jmp reg
                        continue
                    elif len(list(self.function.GetRefsTo(instr.GetOriginEA()))) > 1:
                        #this is a case of switch jump
                        continue
                    elif len(list(self.function.GetRefsTo(instr.GetOriginEA()))) == 1:
                        parent = list(self.function.GetRefsTo(instr.GetOriginEA()))[0][0]
                        if len(list(self.function.GetRefsFrom(parent))) > 1:
                            continue
                    
                    refs_to = list(self.function.GetRefsTo(refs_from[0][0]))
                    
                    if debug:
                        print ">ReduceJMP:Reduce - RefsTo:", refs_to
                    
                    if len(refs_to) == 1 and refs_from[0][0] != self.function.start_ea:
                        if debug:
                            print ">ReduceJMP:Reduce - Found jmp to be removed @ [%08x]" % instr.GetOriginEA()
                            print ">ReduceJMP:Reduce - Orig[%08x] RefTo[%08x] RefFrom[%08x]" % (instr.GetOriginEA(), -1 if refs_to[0][0] == None else refs_to[0][0], -1 if refs_from[0][0] == None else refs_from[0][0])
                            
                        #if refs_to[0][0] != instr.GetOriginEA():
                        #    #assert
                        #    raise MiscError
                        
                        #Update CFG; remove jmp instruction, update references,
                        #merge BB's and update BB table
                        modified = self.function.RemoveInstruction(instr.GetOriginEA(), bb_ea)
                        changed = modified
                        
                elif not instr.IsCFI():
                    if debug:
                        print ">ReduceJMP:Reduce2 - JMP@[%08x] BB[%08x] Mnem[%s]"  % (instr.GetOriginEA(), bb_ea, instr.GetMnem())
                        
                    refs_from = list(self.function.GetRefsFrom(instr.GetOriginEA()))
                    
                    if debug:
                        print ">ReduceJMP:Reduce - RefsFrom:", refs_from
                    
                    if len(refs_from) != 1:
                        #assert rule
                        print "@ %08x" % instr.GetOriginEA(), refs_from
                        raise MiscError
                    
                    if len(list(self.function.GetRefsTo(instr.GetOriginEA()))) > 1:
                        #this is a case of switch jump
                        continue
                    elif len(list(self.function.GetRefsTo(instr.GetOriginEA()))) == 1:
                        parent = list(self.function.GetRefsTo(instr.GetOriginEA()))[0][0]
                        if len(list(self.function.GetRefsFrom(parent))) > 1:
                            continue
                    
                    refs_to = list(self.function.GetRefsTo(refs_from[0][0]))
                    
                    if debug:
                        print ">ReduceJMP:Reduce - RefsTo:", refs_to
                    
                    if len(refs_to) == 1 and refs_from[0][0] != self.function.start_ea:
                        if debug:
                            print ">ReduceJMP:Reduce - Found block to be merged @ [%08x]" % instr.GetOriginEA()
                            print ">ReduceJMP:Reduce - Orig[%08x] RefTo[%08x] RefFrom[%08x]" % (instr.GetOriginEA(), refs_to[0][0] if refs_to[0][0] != None else -1, refs_from[0][0] if refs_from[0][0] != None else -1 )   
                        
                        self.function.basic_blocks[bb_ea].extend(self.function.basic_blocks[refs_from[0][0]][:])
                        del self.function.basic_blocks[refs_from[0][0]]
                        
                        changed = True                        
                        modified = True
        
        return modified


    def JccReduce(self, function=None):
        if function != None:
            self.function = function
        if self.function == None:
            raise MiscError
        
        modified = False
        for bb_ea in self.function.DFSFalseTraverseBlocks():
            modified |= self.JccReduceBlock(self.function.GetBBInstructions(bb_ea))
            
        if modified:
            self.function.AssertCFGStructure()
        return modified
    
 
    def JccReduceBlock(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
            
        if len(bb) < 1:
            return False
        
        modified = False
        
        #get last instruction from block (this is only place for branch
        #instruction)
        last_ins = bb[-1]
        if last_ins.IsJcc():
            jcc_taint = last_ins.GetTaintInfo()
            
            check_flags = jcc_taint.GetFlags('test_f')
            find_flags = []
            
            if check_flags == None:
                print 'No FLAGS FOR JCC [%08x]' % last_ins.GetOriginEA()
                return False
            
            tmp_flags = [f for f in check_flags]
            for f in tmp_flags:
                for syn in jcc_synonym[last_ins.GetMnem()]:
                    if syn.find(f.lower()) > 0:
                        if syn[1] == "n":
                            find_flags.append(f.lower())
                        else:
                            find_flags.append(f.upper())
                        break
            
            branch = True
            
            if len(find_flags) < 1:
                #CURENTLY NOT SUPPORTED (JLE AND SUCH SF OF)
                return False
                #raise MiscError
            
            if debug:
                print ">ReduceJMP:JccReduceBlock - Found JCC block @ [%08x] @ [%08x]" % (bb[0].GetOriginEA(), last_ins.GetOriginEA())
                print ">ReduceJMP:JccReduceBlock - [%s] Looking for: [%s] " % (last_ins.GetMnem(), check_flags)
            
            for instr in bb[::-1][1:]:
                taint = instr.GetTaintInfo()
                
                #modif_f
                #f_vals
                f_vals = taint.GetFlags('f_vals')
                modif_f = taint.GetFlags('modif_f')
                flag_def = {}
                
                if f_vals != None:
                    ff = find_flags[:]
                    for flag in find_flags:
                        match = re.search(flag, f_vals, re.IGNORECASE)
                        if match != None:
                            ff.remove(flag)
                            match = match.group()
                            
                            if debug:
                                print ">ReduceJMP:JccReduceBlock - ", branch, match, flag, '[%08x]' % taint.GetOriginEA()
                                
                            branch = branch and (match == flag)
                                
                    find_flags = ff
                    
                if len(find_flags) == 0:
                    if debug:
                        print ">ReduceJMP:JccReduceBlock - PRUNNING JCC BLOCK @ [%08x] [%d]!" % (last_ins.GetOriginEA(), branch)
                        print ">ReduceJMP:JccReduceBlock - CALLING funct[%08x] last_ins[%08x] branch[%d]" % (self.function.start_ea, last_ins.GetOriginEA(), branch)
                    
                    
                    self.function.RemoveJccPath(last_ins.GetOriginEA(), not branch)
                    last_ins.SetMnem("jmp")
                    last_ins.SetOpcode("\eb\ef")
                    last_ins.SetDisasm('jmp 0xdeadbeef')
                    
                    return True
                    #return (last_ins.GetOriginEA(), branch)
                    
                undecided = False
                
                if modif_f != None:
                    ff = find_flags[:]
                    for flag in find_flags:
                        match = re.search(flag, modif_f, re.IGNORECASE)
                        if match != None:
                            ff.remove(flag)
                            undecided = True
                            
                    find_flags = ff
                    
                if undecided == True:
                    break
            else:
                undecided = True
        
        #return (None, None)
        return False
        
    def JccReduceComplementary(self, function=None):
        if function != None:
            self.function = function
        if self.function == None:
            raise MiscError
        
        modified = False
        for bb_ea in self.function.DFSFalseTraverseBlocks():
            modified |= self.JccReduceComplementaryBlock(self.function.GetBBInstructions(bb_ea))
        
        if modified:
            self.function.AssertCFGStructure()
        return modified
    
    def JccReduceComplementaryBlock(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
            
        if len(bb) < 1:
            return False
        
        modified = False
        
        #get last instruction from block (this is only place for branch
        #instruction)
        last_ins = bb[-1]
        if last_ins.IsJcc():
            
            refs = list( self.function.GetRefsFrom(last_ins.GetOriginEA()) )
            if len(refs) == 1:
                last_ins.SetMnem('jmp')
                last_ins.SetOpcode('\xeb\xef')
                last_ins.SetDisasm('jmp 0xdeadbeef')
                
                return True
            
            jcc_taint = last_ins.GetTaintInfo()
            jcc1_mnem = last_ins.GetMnem().lower()
            
            check_flags = jcc_taint.GetFlags('test_f')
            if check_flags == None:
                print ">ReduceJMP:JccReduceComplementaryBlock - No flags @ [%08x]" % last_ins.GetOriginEA()
                return False
            
            find_flags = [f for f in check_flags]
            find_flags.sort()
            
            branch = True
            
            if len(find_flags) < 1:
                raise MiscError
            
            if debug:
                print ">ReduceJMP:JccReduceComplementaryBlock - Found JCC block @ [%08x] @ [%08x]" % (bb[0].GetOriginEA(), last_ins.GetOriginEA())
                print ">ReduceJMP:JccReduceComplementaryBlock - [%s] Looking for: [%s] " % (last_ins.GetMnem(), check_flags)
            
            false_path = refs[1][0] if refs[0][1] else refs[0][0]
            true_path = refs[1][0] if refs[1][1] else refs[0][0]
            
            false_bb = list(self.function.GetBBInstructions(false_path))
            
            if false_bb[0].IsJcc():
                jcc2_mnem = false_bb[0].GetMnem().lower()
                
                if jcc2_mnem in jcc_map[jcc1_mnem]:
                    refs2 = list( self.function.GetRefsFrom(false_bb[0].GetOriginEA()) )
                    false_path2 = refs2[1][0] if refs2[0][1] else refs2[0][0]
                    true_path2 = refs2[1][0] if refs2[1][1] else refs2[0][0]
                    
                    if true_path2 == true_path:
                        #we should replace previous jcc with jmp
                        self.function.RemoveJccPath(last_ins.GetOriginEA(), False)
                        last_ins.SetMnem('jmp')
                        last_ins.SetOpcode('\xeb\xef')
                        last_ins.SetDisasm('jmp 0xdeadbeef')
                        modified = True
                        
                        if debug:
                            print ">ReduceJMP:JccReduceComplementaryBlock - Replaced JCC @ [%08x] with JMP" % (last_ins.GetOriginEA())
            
            fpath_instr = false_bb[-1]
            if not modified and fpath_instr.IsJcc(): #check false path for optimization
                jcc2_mnem = fpath_instr.GetMnem().lower()
                jcc2_taint = fpath_instr.GetTaintInfo()
                
                flags1 = ''.join(find_flags)
                flags1_set = set(find_flags)
                
                flags2 = [f for f in jcc2_taint.GetFlags('test_f')]
                
                #flags2_map = dict([(x,True) for x in flags2])
                flags2.sort()
                flags2 = ''.join(flags2)
                flags2_set = set(flags2) 
                
                if flags1_set.issuperset(flags2_set):
                    #now check it flags2 are tainted before somewhere in the block
                    
                    is_tainted = False
                    for instr in false_bb[:-1]:
                        taint = instr.GetTaintInfo()
                        
                        modif_f = taint.GetFlags('modif_f')
                        modif_f = "" if modif_f == None else modif_f
                        
                        if flags2_set.issubset(set([f for f in modif_f])):
                            is_tainted = True
                            break
                    
                    if not is_tainted:
                        if jcc_synonym.has_key(jcc1_mnem) and (jcc2_mnem in jcc_synonym[jcc1_mnem]):
                            #this means that they depend on same flags
                            #we are in False branch so this jcc will be also False
                            self.function.RemoveJccPath(fpath_instr.GetOriginEA(), False)
                            fpath_instr.SetMnem('jmp')
                            fpath_instr.SetOpcode('\xeb\xef')
                            fpath_instr.SetDisasm('jmp 0xdeadbeef')
                            modified = True
                            
                            if debug:
                                print ">ReduceJMP:JccReduceComplementaryBlock - Replaced JCC @ [%08x] with JMP" % (fpath_instr.GetOriginEA())
                                
                        elif jcc2_mnem in jcc_map[jcc1_mnem]:
                            #this means that they depend on opposite flags
                            #we are in False branch so this jcc will be True
                            self.function.RemoveJccPath(fpath_instr.GetOriginEA(), True)
                            fpath_instr.SetMnem('jmp')
                            fpath_instr.SetOpcode('\xeb\xef')
                            fpath_instr.SetDisasm('jmp 0xdeadbeef')
                            modified = True
                            
                            if debug:
                                print ">ReduceJMP:JccReduceComplementaryBlock - Replaced JCC @ [%08x] with JMP" % (fpath_instr.GetOriginEA())
                    
        return modified
