'''
    Function representation class
'''

import copy
import array
import re
import pickle
import os
import zlib

import idc
import idautils
import idaapi

from Instruction import Instruction
import CFGOptimization
import CodeOptimization

jcc = ['ja', 'jae', 'jb', 'jbe', 'jc', 'jcxz', 'jecxz', 'je', 'jg', 'jge', 'jl', 'jle', 'jna', 'jnae', 'jnb', 'jnbe', 'jnc', 'jne', 'jng', 'jnge', 'jnl', 'jnle', 'jno', 'jnp', 'jns', 'jnz', 'jo', 'jp', 'jpe', 'jpo', 'js', 'jz']
rets = ['ret', 'retn', 'retf']

#Set to 1 if you want to enable debugging output.
debug = 0

class MiscError(Exception):
    def __init__(self):
        return
class RefResolver(Exception):
    def __init__(self):
        return


def LoadSavedFunctions(ea=None):
    functions = {}

    opty_dir = idc.GetIdbPath()
    opty_dir = opty_dir[:opty_dir.rfind(os.sep)] + os.sep + "optimice_%s" % idc.GetInputFile() + os.sep
    if not os.path.isdir(opty_dir):
        return None

    if ea == None:
        for fname in os.listdir(opty_dir):
            if re.match(r"Function_[0-9ABCDEF]+\.pickle", fname) != None:
                f_ea = re.match(r"Function_([0-9ABCDEF]+)\.pickle", fname).group(1)
                fp = open(opty_dir + fname, "rb")
                function = pickle.loads(zlib.decompress(fp.read()))
                fp.close()
                
                functions[f_ea] = function
        
    else:
        fname = "Function_%08x.pickle" % (idc.GetInputFile(), ea)
        
        try:
            fp = open(opty_dir + fname, "r")
            function = pickle.loads(zlib.decompress(fp.read()))
            fp.close()
        
            functions[ea] = function
            
        except:
            return None
        
    return functions
        

    
class Function:
    """Function graph abstraction"""
    
    def __init__(self, startEA=None):
        self.save_fname = ''
        
        self.start_ea = None       #start addr of function
        self.addr_done = {}     #{} of done blocks; key=ea, value=bb addr that ea belongs to
        self.addr_todo = []     #blocks todo
        self.addr_appended_len = 0
        
        self.function_calls = {}#address of call and destination
        self.fake_ret = []      #list of addresses of fake RET opcodes
        
        #bb graph edges
        self.refs_to = {}
        self.refs_from = {}
        
        self.basic_blocks = {}  #key: bb addr, value: [] of instructions
        self.current_block = 0  #address of current block
        
        if startEA != None:
            self.start_ea = startEA
            self.startAnalysis(self.start_ea)
        

    def SaveState(self):
        if self.save_fname == "":
            opty_dir = idc.GetIdbPath()
            opty_dir = opty_dir[:opty_dir.rfind(os.sep)] + os.sep + "optimice_%s" % idc.GetInputFile()
            if not os.path.isdir(opty_dir):
                os.mkdir(opty_dir)
            self.save_fname = "%s%sFunction_%08x.pickle.zlib" % (opty_dir, os.sep, self.start_ea)
        
        fw = open(self.save_fname, "wb+")
        fw.write(zlib.compress(pickle.dumps(self)))
        fw.close()
        
        print ">Function:SaveState - File [%s] saved @ [%s]" % (self.save_fname, os.getcwd())

    def GetRefsTo(self, ea_to):
        if not self.refs_to.has_key(ea_to):
            print "Warning!: [%08x] has no refs to, this is OK only for start_ea of function" % ea_to
            return
        
        for ea in self.refs_to[ea_to]:
            yield (ea, self.refs_to[ea_to][ea])
        
        return
    
    def GetRefsFrom(self, ea_from):
        for ea in self.refs_from[ea_from]:
            yield (ea, self.refs_from[ea_from][ea])
        
        return

    def AddRefsTo(self, ref_to, ref_from, bool=False):
        '''
            Add reference that ref_from points to ref_to.
            For reverse graph traversal (bottom up); (ref_from1, ..., ref_fromN) -> ref_to.
        '''
        
        if debug:
            print ">Function:AddRefsTo - ref_to[%08x] ref_from[%08x]" % (ref_to if ref_to != None else 0, ref_from if ref_from != None else 0)
        
        if self.refs_to.has_key(ref_to):
            if not self.refs_to[ref_to].has_key(ref_from):
                self.refs_to[ref_to][ref_from] = bool
        else:
            self.refs_to[ref_to] = {ref_from:bool}
        return
    
    
    def AddRefsFrom(self, ref_from, ref_to, bool=False):
        '''
            Add reference that key points to val.
            Bool signifies if jcc reference is True or False branch.
            For normal graph traversal (top down); key -> (val1, ..., valN).
        '''
        
        if debug:
            print ">Function:AddRefsFrom - ref_from[%08x] ref_to[%08x]" % (ref_from if ref_from != None else 0, ref_to if ref_to != None else 0)
            
        if self.refs_from.has_key(ref_from):
            if not self.refs_from[ref_from].has_key(ref_to):
                self.refs_from[ref_from][ref_to] = bool
        else:
            self.refs_from[ref_from] = {ref_to:bool}
        return
    
    def EndPath(self, ref_remove):
        if len(self.refs_from[ref_remove]) != 1:
            raise MiscError
            
        for ref_from in self.refs_from[ref_remove].iterkeys():
            if debug:
                print ">Function:EndPath - Deleting reference to[%08x] from[%08x]" % (ref_from if ref_from != None else 0, ref_remove if ref_remove != None else 0)
            del self.refs_to[ref_from][ref_remove]
            
        del self.refs_from[ref_remove]

    def DelRefs(self, ref_remove):
        '''
            Delete intermediary node eg. 1->2->3 => 1->3
        '''
        if len(self.refs_from[ref_remove]) != 1:
            raise MiscError
        
        ref_from = self.refs_from[ref_remove].keys()[0]
        
        if debug and ref_from != self.start_ea:
            print ">Function:DelRefs - Removing references to location [%08x]" % ref_remove
            if self.refs_to.has_key(ref_remove):
                print ">Function:DelRefs - RefsTo:", ', '.join(['%08x' % x for x in self.refs_to[ref_remove] if x!=None])
            else:
                print ">Function:DelRefs - RefsTo: None, Removing function head", 
            print ">Function:DelRefs - RefsFrom:", ', '.join(['%08x' % x for x in self.refs_from[ref_remove] if x!=None])
        
        #start by establishin references from blink<->flink
        #if this instruction is function head, skip this case and make next reference function head
        if ref_remove != self.start_ea:
            for ref_to in self.refs_to[ref_remove]:
                if debug:
                    print ">Function:DelRefs - Adding reference from[%08x] to[%08x]" % (ref_to if ref_to != None else 0, ref_from if ref_from != None else 0)
                    print ">Function:DelRefs - Adding reference from[%08x] to[%08x]" % (ref_from if ref_from != None else 0, ref_to if ref_to != None else 0)
                
                try:
                    self.AddRefsFrom(ref_to, ref_from, self.refs_from[ref_to][ref_remove])
                    self.AddRefsTo(ref_from, ref_to, self.refs_to[ref_remove][ref_to])
                except:
                    print "EXCEPTION ref_to[%08x] ref_from[%08x] ref_remove[%08x]" % (ref_to, ref_from, ref_remove)
                    print 'REFS FROM:', ', '.join([ '[%08x]:[%08x]' % (x, self.refs_from[ref_to][x]) for x in self.refs_from[ref_to].keys() ])
                    print 'REFS TO:', ', '.join([ '[%08x]:[%08x]' % (x, self.refs_to[ref_remove][x]) for x in self.refs_to[ref_remove].keys() ]) 
                    self.AddRefsFrom(ref_to, ref_from, self.refs_from[ref_to][ref_remove])
                    self.AddRefsTo(ref_from, ref_to, self.refs_to[ref_remove][ref_to])
        
        #if this is function head, declare ref_from new function head
        if self.start_ea == ref_remove:
            if debug:
                print ">Function:DelRefs - New start_ea = [%08x]" % ref_from
                
            self.start_ea = ref_from
        
        #if not delete all references to ref_remove
        else:
            for ref_to in self.refs_to[ref_remove].iterkeys():
                if debug:
                    print ">Function:DelRefs - Deleting reference from[%08x] to[%08x]" % (ref_to if ref_to != None else 0, ref_remove if ref_remove != None else 0)
                del self.refs_from[ref_to][ref_remove]
            
        if debug:
            print ">Function:DelRefs - Removing recap:",
            if self.refs_to.has_key(ref_remove):
                print ">Function:DelRefs - ", self.refs_to[ref_remove]
                for x in self.refs_to[ref_remove].iterkeys():
                    print ">Function:DelRefs - Type:", type(x), "[%08x]" % x if x!=None else 0
                    for y in self.refs_from[x].iterkeys():
                        print ">Function:DelRefs ->%08x" % y if y!=None else 0
                
        #
        for ref_from in self.refs_from[ref_remove].iterkeys():
            if debug:
                print ">Function:DelRefs - Deleting reference to[%08x] from[%08x]" % (ref_from if ref_from != None else 0, ref_remove if ref_remove != None else 0)
            del self.refs_to[ref_from][ref_remove]
        
        if debug:
            print ">Function:DelRefs - Removing recap:",
            print self.refs_from[ref_remove]
            for x in self.refs_from[ref_remove].iterkeys():
                print ">Function:DelRefs - Type:", type(x), "[%08x]" % x if x!=None else 0
                for y in self.refs_to[x].iterkeys():
                    print ">Function:DelRefs ->%08x" % y if y!=None else 0
            print ">Function:DelRefs - Removing all traces to [%08x]" % ref_remove if ref_remove != None else 0
            
        if self.refs_to.has_key(ref_remove):
            del self.refs_to[ref_remove]
        if self.refs_from.has_key(ref_remove):
            del self.refs_from[ref_remove]
        
        if self.addr_done.has_key(ref_remove):
            del self.addr_done[ref_remove]
        
        return


    def RemoveJccPath(self, remove_ea, path):
        if debug:
            print ">Function:RemoveJccPath - Starting RemoveJcc @ [%08x] deleting %d" % (remove_ea, path)
            blockea = self.DFSBBSearchHead(remove_ea)
            blocks = self.GetBBInstructions(blockea)
            for blok in blocks:
                print ">Function:RemoveJccPath - Mnem:", blok.GetMnem()
        
        addr_todo = [remove_ea]
        addr_done = {}
        
        refs = self.refs_from[remove_ea]
        keys = [key for key in refs.keys() if key != None and refs[key] == path]
        if len(keys) < 1:
            raise MiscError
        
        for key in refs.keys():
            if key != None and refs[key] != path:
                self.refs_from[remove_ea][key] = True 
        
        if debug:
            print ">Function:RemoveJccPath - refs:",refs
            print ">Function:RemoveJccPath - keys:",keys
        
            if len(keys) > 1:
                raise MiscError
        
        for key in keys:
            if debug:
                print ">Function:RemoveJccPath - DELETING [%08x]" % key
            
            del self.refs_from[remove_ea][key]
            del self.refs_to[key][remove_ea]
            
        #take case of situation when jcc generates only one refs_from or
        #when there is single entry in addr_todo list
        if len(self.addr_todo) > 1:
            if self.addr_todo[-1] == keys[0]:
                self.addr_todo.pop(-1)
                
                if debug:
                    print ">Function:RemoveJccPath - addr_todo.pop(-1)"
                
            elif self.addr_todo[-2] == keys[0]:
                self.addr_todo.pop(-2)
                
                if debug:
                    print ">Function:RemoveJccPath - addr_todo.pop(-2)"
                    
        elif len(self.addr_todo) > 0:
            if self.addr_todo[-1] == keys[0]:
                
                if debug:
                    print ">Function:RemoveJccPath - addr_todo.pop(-1)"
                    
                self.addr_todo.pop(-1)
                
        return


    def ReplaceInstruction(self, ea, instr, bb_ea=None):
        '''
            TODO
        '''
        if bb_ea == None:
            bb_ea = self.DFSBBSearchHead(ea)
        
        bb_len = len(self.basic_blocks[bb_ea])
        for location in xrange(0, bb_len):
            if self.basic_blocks[bb_ea][location].GetOriginEA() == ea:
                refs_from = list(self.GetRefsFrom(ea))
                refs_to = list(self.GetRefsTo(ea))
                
                if len(refs_from) > 1:
                    print ">Function:RemoveJccPath - refs_from:", refs_from
                    print ">Function:RemoveJccPath - ", ', '.join(['%08x' % x[0] for x in refs_from])
                    print ">Function:RemoveJccPath - [%08x] [%08x]" % (ea, bb_ea)
                    raise MiscError
                
                for item in refs_from:
                    refs_to_target = self.GetRetfTo(item[0])
                    #blablabla TODO
                    
                self.basic_blocks[bb_ea].pop(location)
                self.basic_blocks[bb_ea].insert(location, instr)
                
                break
            
        return


    def RemoveInstruction(self, ea, bb_ea=None):
        '''
            TODO
        '''
        if bb_ea == None:
            bb_ea = self.DFSBBSearchHead(ea)
        
        bb_len = len(self.basic_blocks[bb_ea])
        for location in xrange(0, bb_len):
            if self.basic_blocks[bb_ea][location].GetOriginEA() == ea:
                refs_from = list(self.GetRefsFrom(ea))
                
                if len(refs_from) > 1:
                    print ">Function:RemoveInstruction - ", refs_from
                    print ">Function:RemoveInstruction - ", ', '.join(['%08x' % x[0] for x in refs_from])
                    print ">Function:RemoveInstruction - [%08x] [%08x]" % (ea, bb_ea)
                    raise MiscError
                
                test = self.basic_blocks[bb_ea].pop(location)
                old_bb_len = len(self.basic_blocks[bb_ea])
                self.DelRefs(ea)
                
                if debug:
                    print ">Function:RemoveInstruction - mnem[%s] ea[%08x]" % (test.GetMnem(), test.GetOriginEA())
                
                if location == 0 and ea == self.start_ea:
                    break
                
                elif location == 0 and old_bb_len > 0:
                    #if len(self.basic_blocks[bb_ea]) > 1:
                    try:
                        new_bb_head = self.basic_blocks[bb_ea][0].GetOriginEA()
                    except:
                        print hex(ea), hex(bb_ea)
                        raise 
                    self.basic_blocks[new_bb_head] = copy.deepcopy(self.basic_blocks[bb_ea])
                    
                    if debug:
                        print ">Function:RemoveInstruction0 - Removing BasicBlock @ [%08x]" % bb_ea
                    
                    del self.basic_blocks[bb_ea]
                    
                elif location == 0:
                    if debug:
                        print ">Function:RemoveInstruction - Removing BasicBlock @ [%08x]" % bb_ea
                        
                    del self.basic_blocks[bb_ea]
                    
                elif location == (bb_len-1) and len(self.basic_blocks[bb_ea]) > 0:
                    if debug:
                        print ">Function:RemoveInstruction - !Merging blocks [%08x]" % (test.GetOriginEA())
                    #in this case try to merge blocks
                    last_ea = self.basic_blocks[bb_ea][-1].GetOriginEA()
                    refs_from = list(self.GetRefsFrom(last_ea))
                    
                    if len(refs_from) != 1:
                        return False
                        raise MiscError
                    
                    refs_to = list(self.GetRefsTo(refs_from[0][0]))
                    
                    if len(refs_to) == 1:
                        if self.basic_blocks.has_key(refs_from[0][0]):
                            self.basic_blocks[bb_ea].extend(self.basic_blocks[refs_from[0][0]][:])
                            
                            if debug:
                                print ">Function:RemoveInstruction - Removing BasicBlock @ [%08x]" % refs_from[0][0]
                            
                            del self.basic_blocks[refs_from[0][0]]
                        elif refs_from[0][0] == None:
                            pass
                        else:
                            raise MiscError
                break
            
        #self.CleanUp()
        
        return True


    def startAnalysis(self, startEA):
        '''
        Begins asm2asmCFG translation.
        Should support pause/resume operation.
        '''
        
        #INITIALIZE OPTIMIZATION ENGINES
        cfg_optimization = CFGOptimization.ReduceJMP(self)
        code_optimization = CodeOptimization.PeepHole(self)
        dead_code = CodeOptimization.DeadCodeElimination(self)
        
        if startEA != None:
            self.addr_todo.append(startEA)
            if self.start_ea == None:
                self.start_ea = startEA
            else:
                self.current_block = startEA
                
            self.current_block = startEA
            self.basic_blocks[startEA] = []
        
        prev_block_ea = self.current_block
        
        if len(self.addr_done) > 0:
            self.UpdateAddrDone()
        
        while len(self.addr_todo) > 0:
            ea = self.addr_todo.pop()
            
            if self.addr_done.has_key(ea):
                if debug:
                    print ">Function:startAnalysis - !Skipping over @ %08x" % ea
                    
                self.current_block = 0
                continue
            self.addr_done[ea] = -1         #unknown currently
            
            self.addr_appended_len = self._fillInstructionData(ea)
            
            #After we build a BB we optimize it
            #Note: There is a special case when next block is result of
            #   CodeReftTo(ea) > 1 splitting, in that case this will be executed
            #   only after new block is created and first instruction finishes
            #   but this does not affect DFS algorithm so it's ok
            if self.current_block != prev_block_ea:
                if prev_block_ea != 0:
                    if debug:
                        print ">Function:startAnalysis - !Starting BB optimization @ %08x != %08x" % (prev_block_ea, self.current_block)
                    
                    #DO OPTIMIZATIONS
                    while True:
                        modified = False
                        if self.basic_blocks.has_key(prev_block_ea):
                            modified |= dead_code.ReduceBB(self.basic_blocks[prev_block_ea])
                        if self.basic_blocks.has_key(prev_block_ea):
                            modified |= code_optimization.ReduceBB(self.basic_blocks[prev_block_ea])
                        if self.basic_blocks.has_key(prev_block_ea):
                            modified |= cfg_optimization.JccReduceBlock(self.basic_blocks[prev_block_ea])
                            
                        if not modified:
                            break
                    
                prev_block_ea = self.current_block
        
        self.addr_appended_len = 0
        self.AssertCFGStructure()
        
        if debug:
            print map(hex, self.basic_blocks)
            self.PrintBlocks()


    def _fillInstructionData(self, ea):
        '''
        Populate instruction information.
        Add self.addr_todo info.
        '''
        
        if debug:
            print '>Function:_fillInstructionData - Filling @ [%08x]' % ea
        
        refs_appended = 0
        
        if idc.isCode(idc.GetFlags(ea)) == False:
            code_dead = 0
            
            #if a current ea is not instruction, try to make it into one
            if idc.MakeCode(ea) == False:
                for mark in xrange(ea, ea+0x10):
                    idc.MakeUnknown(mark, 0x1, idc.DOUNK_SIMPLE)
                if idc.MakeCode(ea) == False:
                    code_dead = 1

            #unable to disasemble current addr, make it ret instruction and add block
            if code_dead == 1:
                if debug:
                    print ">Function:_fillInstructionData - Dead Instruction @ [%08x]" % ea
                
                if self.current_block == 0:
                    self.current_block = ea
                self.addr_done[ea] = self.current_block
                    
                instr = Instruction(ea)
                instr.SetOpcode('\xc3')
                instr.SetMnem('retn')
                instr.SetDisasm('retn')
                instr.SetIsModified(True)
                instr.SetComment('Artificial: Unable to disasm original opcode!')
                
                try:
                    self.basic_blocks[self.current_block].append(instr)
                except:
                    self.basic_blocks[self.current_block] = [instr]
                    
                self.current_block = 0
                self.fake_ret.append(ea)
                
                #Add references to CFG
                self.AddRefsTo(None, ea, True)
                self.AddRefsFrom(ea, None, True)
                
                return refs_appended #done with current instruction
            
            else:
                if debug:
                    print ">Function:_fillInstructionData - Code resurected @ [%08x] [%s]" % (ea, idc.GetMnem(ea))

        idc.OpHex(ea, -1) #convert to simple disasm
        mnem = idc.GetMnem(ea)
        
        instr = Instruction()
        
        #should we create new basic block
        create_new_bb = 0
        
        refs = list(idautils.CodeRefsFrom(ea, 1))
        
        if self.current_block == 0:
            self.current_block = ea
            self.addr_done[ea] = self.current_block
            
            if debug:
                print ">Function:_fillInstructionData - Creating new block @ [%08x]" % ea

        refs_to = list(idautils.CodeRefsTo(ea, 1))
        
        #THIS SHOULD BE LEFT OUT, case: there are refs_to that originate form fake/unreachable code
        #for ref in idautils.CodeRefsTo(ea, 0):
        #    self.AddRefsTo(ref, ea)
        #    self.AddRefsFrom(ea, ref, True)
            
        if len(refs_to) > 1 and ea != self.start_ea:
            #this is a case when there are refs_to but we already created new bb
            if self.current_block != ea:
                if debug:
                    print ">Function:_fillInstructionData - RefsTo len[%d] ref[%08x]" % (len(refs_to), refs_to[0])
                    
                #if current_block != ea then optimize current_block before creating new
                #if self.current_block != 0:
                #    self.peepHoleOptimization(self.current_block)
                #    pass
                self.current_block = ea
                
                if debug:
                    print ">Function:_fillInstructionData - Creating new block @ [%08x]" % ea
        
        refs = list(idautils.CodeRefsFrom(ea, 1))
            
        #populate common data
        instr.SetOriginEA(ea)
        instr.SetMnem(mnem)
        instr.SetDisasm(idc.GetDisasm(ea))
        instr.SetOpcode(''.join(chr(idc.Byte(ea+x)) for x in xrange(0, idc.ItemSize(ea))))
        instr.SetOpnd(idc.GetOpnd(ea, 0), 1)
        instr.SetOpndType(idc.GetOpType(ea, 0), 1)
        
        op_val = idc.GetOperandValue(ea, 0)
        op_mask = 0
        op_size = 0
        if idaapi.cmd[0].dtyp == idaapi.dt_byte:
            op_mask = 0xff
            op_size = 1
        elif idaapi.cmd[0].dtyp == idaapi.dt_word:
            op_mask = 0xffff
            op_size = 2
        elif idaapi.cmd[0].dtyp == idaapi.dt_dword:
            op_mask = 0xffffffffL
            op_size = 4
        elif idaapi.cmd[0].dtyp == idaapi.dt_qword:
            op_mask = 0xffffffffffffffffL
            op_size = 8
        else:
            raise MiscError
        op_val &= op_mask
        
        instr.SetOpndSize(op_size, 1)
        instr.SetOpndValue(op_val, 1)
        instr.SetComment(idc.Comment(ea))
        
        #what to add to addr_todo
        if mnem == 'call':
            if debug:
                print ">Function:_fillInstructionData - CALL instr @ [%08x]" % ea
            
            #not after all, seems redundant 
            #create_new_bb = 1
            
            if len(refs) < 2:
                #we are missing a ref, 2 cases
                
                if False and instr.GetOpnd(1) == '$+5':
                    #NOTE: !this should be removed
                    #NOTE: special care to be taken, constant should be saved as literal and at assembly time resolved as constant
                    if debug:
                        print ">Function:_fillInstructionData - Call2Push @ [%08x]" % ea
                        
                    #create_new_bb = 0
                    
                    instr.SetMnem('push')
                    instr.SetDisasm('push %08xh' % (ea + 5))
                    instr.SetOpnd('%08xh' % (ea + 5), 1)
                    instr.SetOpndType(5, 1)
                    instr.SetOpndValue(ea+5, 1)
                    instr.SetIsModified(True)
                    instr.SetComment('Artificial: Gen from call $+5')
                    instr.SetOpcode(Assembler.SimpleAsm(instr.GetDisasm()))
                    
                    self.addr_todo.append(refs[0])
                    refs_appended += 1
                    
                    #Fill CFG info
                    self.AddRefsTo(refs[0], ea, False)
                    self.AddRefsFrom(ea, refs[0], False)
                    
                elif len(list(idautils.CodeRefsFrom(ea, 0))) > 0:
                    #NOTE: special case, if call(exit) then normal code flow is empty
                    self.function_calls[ea] = instr.GetOpnd(1)
                    
                    #Fill CFG info
                    self.AddRefsTo(None, ea, False)
                    self.AddRefsFrom(ea, None, False)
                    
                    #we have to create new bb after this instruction (we exploit IDA heuristics)
                    #instructions after call don't belong to BB
                    create_new_bb = 1
                    
                else:
                    #This is a case when call destination is unresolvable (eg. call eax)
                    if instr.GetOpnd(1) == '$+5':
                        instr.SetComment('Artificial: Gen from call $+5')
                    
                    self.addr_todo.append(refs[0])
                    refs_appended += 1
                    self.function_calls[ea] = instr.GetOpnd(1)
                    
                    #Fill CFG info
                    self.AddRefsTo(refs[0], ea, False)
                    self.AddRefsFrom(ea, refs[0], False)
                    
                    #raise RefResolver
                
            else:
                #We have 2 refs, as we should
                self.addr_todo.append(refs[0])
                refs_appended += 1
                self.function_calls[ea] = refs[1]
                
                #Fill CFG info
                self.AddRefsTo(refs[0], ea, False)
                self.AddRefsFrom(ea, refs[0], False)
            
        elif mnem == 'jmp':
            if debug:
                print ">Function:_fillInstructionData - JMP @ [%08x]" % ea
            
            if len(refs) == 0:
                #NOTE: special case, ref is unresolvable (eg. jmp eax)
                create_new_bb = 1
                
                #Fill CFG info
                self.AddRefsTo(None, ea, True)
                self.AddRefsFrom(ea, None, True)
                
                #raise RefResolver
                
            elif len(refs) > 1 and idc.GetOpType(ea, 0) == 2:
                #NOTE: switch jump
                expr = idc.GetOpnd(ea, 0)
                m = re.search(r'(\[.*?\])', expr)
                if m != None:
                    expr = m.group()
                    m2 = re.match(r'\[.*?\*.*?\+(.*?)\]', expr)
                    if m2 != None:
                        expr = re.sub(m2.group(1), "SUBS", expr)
                        instr.SetOpnd(expr, 1)
                        
                        self.addr_todo.extend(refs[::-1])
                        refs_appended += len(refs)
                        create_new_bb = 1
                        
                        #add first ref as a "default" jmp
                        for ref in refs:
                            self.AddRefsTo(ref, ea, True)
                            self.AddRefsFrom(ea, ref, True)
                        
                    else:
                        raise MiscError
                else:
                    raise MiscError
                
            else:
                self.addr_todo.append(refs[0])
                refs_appended += 1
                create_new_bb = 1
                
                #Fill CFG info
                self.AddRefsTo(refs[0], ea, True)
                self.AddRefsFrom(ea, refs[0], True)
                
            #check if jmp is loop?
            
        elif mnem in jcc:
            if debug:
                print ">Function:_fillInstructionData - JCC @ [%08x]" % ea
                
            #add CFG edges
            #add normal (False) confition destination
            self.AddRefsTo(refs[0], ea, False)
            self.AddRefsFrom(ea, refs[0], False)
            
            #add True condition destination
            #yes, this case is not always true (jcc $+5)
            if len(refs) > 1:
                self.AddRefsTo(refs[1], ea, True)
                self.AddRefsFrom(ea, refs[1], True)
                
            
            #NOTE: leave, modified flag has special meaning for assembler
            instr.SetIsModified(True)
            
            create_new_bb = 1
            
            #check destination (loop or new block)
            if len(refs) != 2:
                if debug:
                    print ">Function:_fillInstructionData - !WARRNING @ [%08x] JCC with =%d refs [%s]" % (ea, len(refs), mnem)
            
            self.addr_todo.extend(refs[::-1])
            refs_appended += len(refs)
            
        else:
            
            if len(refs) > 1:
                if debug:
                    #eg. loopxx
                    print ">Function:_fillInstructionData - !WARRNING @ [%08x] instr with >1 refs [%s] len(refs)=[%d]" % (ea, mnem, len(refs))
                    print ">Function:_fillInstructionData - \t\t", ', '.join(['%08x' % x for x in refs])
                    
                create_new_bb = 1
                
                #add CFG edges, example instr LOOP
                #add normal (False) confition destination
                self.AddRefsTo(refs[0], ea, False)
                self.AddRefsFrom(ea, refs[0], False)
                
                #add True condition destination
                self.AddRefsTo(refs[1], ea, True)
                self.AddRefsFrom(ea, refs[1], True)
                
            elif len(refs) == 0:
                if debug:
                    print ">Function:_fillInstructionData - !WARRNING @ [%08x] instr with 0 refs [%s]" % (ea, mnem)
                    
                create_new_bb = 1
                
                #add CFG edges
                self.AddRefsTo(None, ea, True)
                self.AddRefsFrom(ea, None, True)
            
            else:
                #regular instruction, one ref_from
                
                next_ea = ea + idc.ItemSize(ea)
                if idc.isCode(idc.GetFlags(next_ea)) == False:
                    if idc.MakeCode(next_ea) == True:
                        next_mnem = idc.GetMnem(next_ea)
                    else:
                        next_mnem = ""
                else:
                    next_mnem = idc.GetMnem(next_ea)
                
                if mnem.lower().find('push') >= 0 and idc.GetOpType(ea, 0) == 5 and next_mnem.lower().find("ret") >= 0 :
                    instr.SetMnem("jmp")
                    instr.SetDisasm("jmp %08xh" % idc.GetOperandValue(ea,0))
                    instr.SetOpcode("\xeb\xef")
                    
                    instr.SetOpnd("%08xh" % idc.GetOperandValue(ea,0), 1)
                    instr.SetOpndType(6, 1)
                    instr.SetOpndValue(idc.GetOperandValue(ea,0), 1)
                    instr.SetIsModified(True)
                    
                    instr.SetComment("-replaced[PUSH/RET]")
                    
                    dest_ea = idc.GetOperandValue(ea,0)
                    self.AddRefsTo(dest_ea, ea, False)
                    self.AddRefsFrom(ea, dest_ea, False)
                    
                    refs = [dest_ea]
                    create_new_bb = 1
                    
                
                #should be false in most cases
                elif mnem.lower().find('ret') >= 0:
                    #special case when ida resolves change of execution with ret
                    
                    #will create new block, and will create references to new location
                    #we treat it like jmp and leave it to optimization to replace instructions
                    
                    instr.SetOriginEA(ea)
                    instr.SetMnem("add")
                    instr.SetDisasm("add     esp, 4")
                    instr.SetOpcode("\x83\xc4\x04")
                    instr.SetOpnd("esp", 1)
                    instr.SetOpndType(1, 1)
                    instr.SetOpndValue(4, 1)
                    
                    instr.SetOpnd("4", 2)
                    instr.SetOpndType(5, 2)
                    instr.SetOpndValue(4, 2)
                        
                    instr2 = Instruction()
                    fake2_ea = ea<<3 | 1
                    
                    instr2.SetOriginEA(fake2_ea)
                    instr2.SetMnem("jmp")
                    instr2.SetDisasm("jmp 0x%08x" % refs[0])
                    instr2.SetOpcode("\xeb\xef")
                    instr2.SetOpnd(str(refs[0]), 1)
                    instr2.SetOpndType(6, 1)
                    instr2.SetOpndValue(refs[0], 1)
                    
                    self.AddRefsTo(fake2_ea, ea, False)
                    self.AddRefsFrom(ea, fake2_ea, False)
                    
                    self.AddRefsTo(refs[0], fake2_ea, False)
                    self.AddRefsFrom(fake2_ea, refs[0], False)
                    
                    if self.basic_blocks.has_key(self.current_block):
                        self.basic_blocks[self.current_block].append(instr)
                    else:
                        self.basic_blocks[self.current_block] = [instr]
                    
                    #this instruction will be added by default case
                    instr = instr2
                        
                    create_new_bb = 1
                    
                else:
                    #add CFG edges
                    instr.SetOpnd(idc.GetOpnd(ea, 1), 2)
                    instr.SetOpndType(idc.GetOpType(ea, 1), 2)
                    
                    op_val = idc.GetOperandValue(ea, 1)
                    op_mask = 0
                    op_size = 0
                    if idaapi.cmd[0].dtyp == idaapi.dt_byte:
                        op_mask = 0xff
                        op_size = 1
                    elif idaapi.cmd[0].dtyp == idaapi.dt_word:
                        op_mask = 0xffff
                        op_size = 2
                    elif idaapi.cmd[0].dtyp == idaapi.dt_dword:
                        op_mask = 0xffffffffL
                        op_size = 4
                    elif idaapi.cmd[0].dtyp == idaapi.dt_qword:
                        op_mask = 0xffffffffffffffffL
                        op_size = 8
                    else:
                        raise MiscError
                    op_val &= op_mask
                    
                    instr.SetOpndSize(op_size, 2)
                    instr.SetOpndValue(op_val, 2)
                    
                    if idc.GetOpnd(ea,2) != '':
                        instr.SetOpnd(idc.GetOpnd(ea, 2), 3)
                        instr.SetOpndType(idc.GetOpType(ea, 2), 3)

                        op_val = idc.GetOperandValue(ea, 2)
                        op_mask = 0
                        op_size = 0
                        if idaapi.cmd[0].dtyp == idaapi.dt_byte:
                            op_mask = 0xff
                            op_size = 1
                        elif idaapi.cmd[0].dtyp == idaapi.dt_word:
                            op_mask = 0xffff
                            op_size = 2
                        elif idaapi.cmd[0].dtyp == idaapi.dt_dword:
                            op_mask = 0xffffffffL
                            op_size = 4
                        elif idaapi.cmd[0].dtyp == idaapi.dt_qword:
                            op_mask = 0xffffffffffffffffL
                            op_size = 8
                        else:
                            raise MiscError
                        op_val &= op_mask
                        
                        instr.SetOpndSize(op_size, 3)
                        instr.SetOpndValue(op_val, 3)
                        
                    self.AddRefsTo(refs[0], ea, False)
                    self.AddRefsFrom(ea, refs[0], False)
            
            #common case, extend DFS list
            #if mnem.find("ret") < 0:
            self.addr_todo.extend(refs[::-1])
            refs_appended += len(refs)
            
        if self.basic_blocks.has_key(self.current_block):
            self.basic_blocks[self.current_block].append(instr)
        else:
            self.basic_blocks[self.current_block] = [instr]
        
        if create_new_bb == 1:
            #self.peepHoleOptimization(self.current_block)
            self.current_block = 0
            
        return refs_appended


    def DFSBBSearchHead(self, find_addr):
        '''
            Find head (start) of basic block that has find_addr as an element.
            
            NOTE: use heuristic that you can discharge/stop analysis when you
                find self.basic_blocks.has_key(head), either addr belogns to
                that block (code path) or not.
            Return: Head of BB that find_addr belongs to.
        '''
        
        if debug:
            print ">Function:DFSBBSearchHead - Searching for block head @ [%08x]" % find_addr
        
        addr_todo = [find_addr]
        addr_done = {}
        
        while len(addr_todo) > 0:
            ea = addr_todo.pop()

            if addr_done.has_key(ea) or ea == None:
                continue
                
            addr_done[ea] = True
            
            if self.basic_blocks.has_key(ea):
                for instr in self.basic_blocks[ea]:
                    if instr.GetOriginEA() == find_addr:
                        if debug:
                            print ">Function:DFSBBSearchHead - !Found BB head @ %08x len[%d] offset[%d]" % (ea, len(self.basic_blocks[ea]), self.basic_blocks[ea].index(instr))
                        return ea
            
            if ea == self.start_ea:
                print "Searching for [%08x] got us to [%08x] (function head), no results" % (find_addr, ea)
                continue
            
            #try to save the situation
            if not self.refs_to.has_key(ea):
                for bb_ea in self.basic_blocks.iterkeys():
                    for item in self.basic_blocks[bb_ea]:
                        if item.GetOriginEA() == find_addr:
                            return bb_ea
                
            if debug:
                print '>Function:DFSBBSearchHead - Located @ [%08x] Refs @ ' % ea,
                print ">Function:DFSBBSearchHead - refs_to:" + ', '.join(['%08x' % x for x in self.refs_to[ea].iterkeys() if type(x) == type(1)])
            
            for addr in self.refs_to[ea].iterkeys():
                if self.basic_blocks.has_key(addr):
                    for instr in self.basic_blocks[addr]:
                        if instr.GetOriginEA() == find_addr:
                            if debug:
                                print ">Function:DFSBBSearchHead - !Found BB head @ %08x len[%d] offset[%d]" % (addr, len(self.basic_blocks[addr]), self.basic_blocks[addr].index(instr))
                            return addr
                    else:
                        if debug:
                            print ">Function:DFSBBSearchHead - Adding [%08x]" % addr
                        addr_todo.append(addr)
                else:
                    if debug:
                        print ">Function:DFSBBSearchHead - Adding [%08x]" % addr
                    addr_todo.append(addr)
                    
            #else:
                #addr_todo.extend(self.refs_to[ea].keys()[::-1])
        
        return None


    def SplitBlock(self, split_addr):
        '''
            Split basic block @ split_addr and create a new basic_blocks[]
            entry.
        '''
        
        if debug:
            print ">Function:SplitBlock - Entry splitting @ [%08x] " % split_addr
        
        if self.basic_blocks.has_key(split_addr):
            if debug:
                print ">Function:SplitBlock - Splitting not needed @ [%08x], EA is head of BB" % split_addr
            return
        
        bb_head = split_addr
        
        orig_head = self.DFSBBSearchHead(split_addr)
        if orig_head == None:
            print ">Function:SplitBlock - Failed @ [%08x]: orig_head=None" % split_addr
            raise MiscError
            #return
        
        if debug:
            print ">Function:SplitBlock - Got orig_head [%08x] " % orig_head
        
        self.basic_blocks[bb_head] = []
        if len(self.basic_blocks[orig_head]) > 0:
            instr = self.basic_blocks[orig_head].pop()
        else:
            print ">Function:SplitBlock - basic_blocks[%08x] empty" % orig_head
            return
        
        while True:
            self.basic_blocks[bb_head].insert(0, instr)
            if instr.GetOriginEA() == bb_head:
                break
            
            instr = self.basic_blocks[orig_head].pop()
        
        if debug:
            print ">Function:SplitBlock - Split @ [%08x]; original @ [%08x]" % (split_addr, orig_head)
        
        return


    def AssertCFGStructure(self):
        '''
            Make sure that CFG structure conforms with basic block rules.
            First we iterate trough whole CFG and split any blocks that have
            code references to the middle of the block.
            Used for debugging.
        '''
        if self.start_ea == None:
            return
        
        if debug:
            print ">Function:AssertCFGStructure - Starting TraverseBlocks @ [%08x]" % self.start_ea
        
        #self.UpdateAddrDone()
        
        addr_todo = [self.start_ea]
        addr_done = {}
        while len(addr_todo) > 0:
            ea = addr_todo.pop()

            if addr_done.has_key(ea) or ea == None:
                continue
                
            addr_done[ea] = True
            
            if debug:
                print ">Function:AssertCFGStructure - Traversing @ %08x" % ea
            
            if not self.basic_blocks.has_key(ea):
                if debug:
                    print ">Function:AssertCFGStructure1 - SplitBlock needed @ [%08x]" % ea
                
                #try:
                self.SplitBlock(ea)
                #except:
                #    print ">Function:AssertCFGStructure - Split EXCEPTION for [%08x] because " % (ea)
                #    print map(hex, self.refs_to[ ea ].keys())
                    

            #check to see if there is isCFI() instruction other than last one
            last_i = self.basic_blocks[ea][-1]
            first_i = self.basic_blocks[ea][0]
            
            for i in self.basic_blocks[ea]:
                if i.GetOriginEA() == self.start_ea:
                    continue
                
                if (i.IsCFI() and not i.IsCall() and not i.IsLoop() and i.GetOriginEA() != last_i.GetOriginEA()) or (len(list(self.GetRefsTo(i.GetOriginEA()))) > 1 and i.GetOriginEA() != first_i.GetOriginEA()):
                    if debug:
                        print ">Function:AssertCFGStructure2 - SplitBlock needed @ [%08x]" % ea
                    self.SplitBlock(i.GetOriginEA())
            
            try:
                addr_ref = self.basic_blocks[ea][-1].GetOriginEA()
            except:
                print ">Function:AssertCFGStructure - [%08x]" % ea
                print ">Function:AssertCFGStructure - ", self.basic_blocks[ea]
                print ">Function:AssertCFGStructure - ", self.basic_blocks[ea][-1]
                raise MiscError
                
            if addr_ref == None:
                continue
            
            #if debug:
                #print ">Function:AssertCFGStructure - Last instruction %s @ [%08x]" % ( self.basic_blocks[ea][-1].GetMnem(), self.basic_blocks[ea][-1].GetOriginEA() )
                #print ">Function:AssertCFGStructure - REFS ", map(hex, self.refs_from[ addr_ref ].iterkeys())
            
            for addr in self.refs_from[ addr_ref ].iterkeys():
                if (addr != None) and (not self.basic_blocks.has_key(addr)):
                    if debug:
                        print ">Function:AssertCFGStructure(for) - SplitBlock needed @ [%08x]" % addr
                    
                    #try:
                    self.SplitBlock(addr)
                    #except:
                    #    print ">Function:AssertCFGStructure - Split EXCEPTION for [%08x] because " % (ea)
                    #    print map(hex, self.refs_to[ ea ].keys())
                    
            #if debug:
                #print ">Function:AssertCFGStructure - Adding: [%s]" % ', '.join(['%08x' % x for x in self.refs_from[ addr_ref ].keys()[::-1] ])
            addr_todo.extend(self.refs_from[ addr_ref ].keys()[::-1])
            
        return


    def TraverseWholeCFG(self):
        '''
            Traverse all instructions in CFG.
            Used for debugging.
        '''
        if self.start_ea == None:
            return
        
        if debug:
            print ">Function:TraverseWholeCFG - Starting TraverseBlocks @ [%08x]" % self.start_ea
        
        addr_todo = [self.start_ea]
        addr_done = {}
        while len(addr_todo) > 0:
            ea = addr_todo.pop()

            if addr_done.has_key(ea) or ea == None:
                continue
                
            addr_done[ea] = True
            
            
            if debug:
                print ">Function:TraverseWholeCFG - Analysis @ [%08x] " % ea
            
            try:
                refs = self.refs_from[ea].keys()
                #NOTE: hex(x) to the rescue if x=None then this will give hint to the 
                print ">Function:TraverseWholeCFG - Instruction @ [%08x] -> Refs @ " % ea, ', '.join(['%08x' % x for x in refs if type(x) == type(1)]),
                if None in refs:
                    print ">Function:TraverseWholeCFG - None"
                else:
                    print
            except:
                #!!!!!!!!!!!!!!!!!!!!!!!!!!!
                if debug:
                    print ">Function:TraverseWholeCFG - ", "NOTICE:"*4, hex(ea), self.refs_from[ea].keys()
                    
                refs = []
                if ea == None:
                    print ">Function:TraverseWholeCFG - Instruction @ [None] -> NULL"
                else:
                    print ">Function:TraverseWholeCFG - Instruction @ [%08x] -> None" % ea
            
            addr_todo.extend(refs[::-1])
        return


    def DFSFalseTraverseBlocks(self):
        '''
            TraverseBlocks and at every block call callback(block_ea).
            callback - function
        '''
        
        if self.start_ea == None:
            return
        
        if debug:
            print ">Function:DFSFalseTraverseBlocks - Starting TraverseBlocks @ [%08x]" % self.start_ea
        
        addr_todo = [self.start_ea]
        addr_done = {}
        while len(addr_todo) > 0:
            ea = addr_todo.pop()
            
            if addr_done.has_key(ea) or ea == None:
                continue
                
            addr_done[ea] = True
            
            
            if debug:
                print ">Function:DFSFalseTraverseBlocks - Analysis @ [%08x] " % ea
            
            try:
                __refs = copy.deepcopy(self.refs_from[ self.basic_blocks[ea][-1].GetOriginEA() ])
            except:
                if debug:
                    print "Exception %08x head %08x" % (ea, self.start_ea)
                    print ', '.join(['%08x'%x for x in self.basic_blocks])
                __refs = copy.deepcopy(self.refs_from[ self.basic_blocks[ea][-1].GetOriginEA() ])
                #print "BB", self.basic_blocks.has_key(ea), "Len:[%d]" % len(self.basic_blocks[ea])
                #print "origin [%08x]" % self.basic_blocks[ea][-1].GetOriginEA()
                #print self.refs_from[ self.basic_blocks[ea][-1].GetOriginEA() ]
                continue
                
            
            yield ea
            
            if self.basic_blocks.has_key(ea) and len(self.basic_blocks[ea]):
                refs = self.refs_from[ self.basic_blocks[ea][-1].GetOriginEA() ]
                
                if debug:
                    print ">Function:DFSFalseTraverseBlocks - ADDING REFS from bb[%08x] instr[%08x]" % (ea, self.basic_blocks[ea][-1].GetOriginEA()), ', '.join(['%08x' % x for x in refs.keys() if x != None])
                
                
                for x in refs.keys():
                    if x != None and refs[x] == True:
                        if not self.basic_blocks.has_key(x):
                            print ">Function:DFSFalseTraverseBlocks - Notice: Reference [%08x] from [%08x] is not a BB head!" % (x, ea)
                        addr_todo.append(x)
                #addr_todo.extend([x for x in refs.keys() if x != None and refs[x] == True ])
                
                for x in refs.keys():
                    if x != None and refs[x] == False:
                        if not self.basic_blocks.has_key(x):
                            print ">Function:DFSFalseTraverseBlocks - Notice: Reference [%08x] from [%08x] is not a BB head!" % (x, ea)
                        addr_todo.append(x)
                #addr_todo.extend([x for x in refs.keys() if x != None and refs[x] == False ])
            else:
                if debug:
                    print ">Function:DFSFalseTraverseBlocks - WEIRD! block ref missing!"
                    
                for x in __refs.keys():
                    if x == None:
                        continue
                    elif not __refs.has_key(x):
                        print ">Function:DFSFalseTraverseBlocks - ERROR: __refs NO key [%08x]" % x
                        continue
                    elif __refs[x] == True:
                        if not self.basic_blocks.has_key(x):
                            print ">Function:DFSFalseTraverseBlocks - Notice: Reference [%08x] from [%08x] is not a BB head!" % (x, ea)
                        addr_todo.append(x)      
            
        return


    def CleanUp(self):
        modified = True
        
        while modified:
            modified = False
            
            alive_blocks = {}
            alive_instr = {}
            
            for bb_ea in self.DFSFalseTraverseBlocks():
                alive_blocks[bb_ea] = True
                
                for instr in self.GetBBInstructions(bb_ea):
                    alive_instr[instr.GetOriginEA()] = True
            
            remove_ea = []
            for bb_ea in self.basic_blocks.iterkeys():
                if not alive_blocks.has_key(bb_ea):
                    remove_ea.append(bb_ea)
            
            if len(remove_ea) > 0:
                modified = True
            for ea in remove_ea:
                if debug:
                    ">Function:CleanUp - Deleting BasicBlock @ [%08x]" % ea
                del self.basic_blocks[ea]
            
            remove_ea = []
            for ea in self.refs_from.iterkeys():
                if not alive_instr.has_key(ea) and ea != None:
                    remove_ea.append(ea)
            
            if len(remove_ea) > 0:
                modified = True
            for ea in remove_ea:
                del self.refs_from[ea]
                
            remove_ea = []
            for ea in self.refs_to.iterkeys():
                if not alive_instr.has_key(ea) and ea != None:
                    remove_ea.append(ea)
            
            if len(remove_ea) > 0:
                modified = True
            for ea in remove_ea:
                del self.refs_to[ea]
            
            for ea in alive_blocks:
                if ea != self.start_ea:
                    refs_to = list(self.GetRefsTo(ea))
                    for x in [x[0] for x in refs_to if x[0] != None]:
                        if not self.refs_from.has_key(x):
                            del self.refs_to[ea][x]
            
        return


    def GetBBInstructions(self, ea):
        if not self.basic_blocks.has_key(ea):
            raise MiscError
        
        for instr in self.basic_blocks[ea]:
            yield instr
        return


    def GetBBLastInstruction(self, ea):
        if not self.basic_blocks.has_key(ea):
            raise MiscError
        
        return self.basic_blocks[ea][-1]


    def PrintBlocks(self):
        '''
            Print basic blocks with instructions.
            We don't care about CFG.
        '''
        print "\n\n>Function:PrintBlocks - Printing Blocks:"
        
        for bb_ea in self.DFSFalseTraverseBlocks():
            print ">Function:PrintBlocks - @ BB[%08x]" % bb_ea
            
            if bb_ea != self.start_ea:
                refs_to = list(self.GetRefsTo(bb_ea))
                print "\t[%08x] Refs_to [%s]" % (bb_ea, ', '.join(['%08x' % x[0] for x in refs_to if x[0] != None]))
                for x in [x[0] for x in refs_to if x[0] != None]:
                    if len(list(self.GetRefsFrom(x))) > 0:
                        print '\t-%08x Alive' % x
                    else:
                        print '\t-%08x DEAD' % x
            print
            
            for instr in self.GetBBInstructions(bb_ea):
                print ">Function:PrintBlocks - In block @ [%08x] [%s] [%s]" % (instr.GetOriginEA(), instr.GetMnem(), instr.GetDisasm())
            
            refs_from = list(self.GetRefsFrom(instr.GetOriginEA()))
            print ">Function:PrintBlocks - @ [%08x] Refs_from [%s]" % (bb_ea, ', '.join(['%08x' % x[0] for x in refs_from if x[0] != None]))
            
            print
            
    def UpdateAddrDone(self):
        self.addr_done = {}
        
        for bb_ea in self.DFSFalseTraverseBlocks():
            for instr in self.GetBBInstructions(bb_ea):
                self.addr_done[instr.GetOriginEA()] = bb_ea
