'''
    Instruction/Data optimization class
'''
import copy
import array
import re

import idc
import idautils
import idaapi

import Instruction
import Assembler

debug = 0
debug_detailed = 0

class MiscError(Exception):
    def __init__(self):
        return


class DeadCodeElimination:
    """Dead Instruction Elimination"""
    
    def __init__(self, function):
        self.function = function

    def ReduceBB(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
        
        if len(bb) < 1:
            return False
        
        remove_todo = []
        
        for offset in xrange(0, len(bb)):
            taint = bb[offset].GetTaintInfo()
            instr = bb[offset]
            
            if debug:
                print ">DeadCodeElimination:ReduceBB - @ [%08x] %s" % (instr.GetOriginEA(), instr.GetDisasm())
            
            if instr.IsCFI():
                if debug:
                    print ">DeadCodeElimination:ReduceBB - skipping CFI..."
                continue
            
            regs_to_check = {}
            regs_todo = 0
            skip_this = 0
            for op in taint.GetDstTaints():
                if op['type'] == 1:
                    if debug and debug_detailed:
                        print ">DeadCodeElimination:ReduceBB - DST# [%s:%d]" % (op['opnd'], op['type'])
                        
                    reg = taint.GetExOpndRegisters(op['opnd'])
                    
                    if len(reg) != 1:
                        if debug and debug_detailed:
                            print ">DeadCodeElimination:ReduceBB - !GetExOpndRegisters returned suspicious data"
                            print ">DeadCodeElimination:ReduceBB - ", op['opnd']
                            print ">DeadCodeElimination:ReduceBB - ", reg
                        
                        skip_this = 1
                        #raise MiscError
                        
                    else:
                        regs_to_check[reg[0][0]] = reg[0][1]
                        regs_todo += 1
                
                elif op['type'] in [2,3,4]:
                    skip_this = 1
                    
                elif op['type'] == None:
                    print ">DeadCodeElimination:ReduceBB - DST# [%s:None]" % (op['opnd'])
                    raise MiscError
                
                else:
                    #well if it taints any other source we let it live :)
                    if debug:
                        print ">DeadCodeElimination:ReduceBB - OP Type [%d] skipped @ [%08x]" % (op['type'], instr.GetOriginEA())
                    skip_this = 1
                
            if skip_this:
                if debug:
                    print ">DeadCodeElimination:ReduceBB - skipping..."
                continue
            
            flags_to_check = {}
            flags_todo = 0
            
            flags = taint.GetFlags('modif_f')
            if flags != None:
                for flag in flags:
                    flags_to_check[flag] = None
                    flags_todo += 1
            
            if debug and debug_detailed:
                print ">DeadCodeElimination:ReduceBB - Regs4Check-> ", regs_to_check
                print ">DeadCodeElimination:ReduceBB - Flags4Check-> ", flags_to_check
            
            #for delta in xrange(offset+1, len(block_taint)):
                #delta_taint = block_taint[delta]
            
            for delta in xrange(offset+1, len(bb)):
                delta_taint = bb[delta].GetTaintInfo()
                if debug and debug_detailed:
                    print ">DeadCodeElimination:ReduceBB - ", len(bb), delta, bb[delta].GetDisasm()
                
                if flags_todo > 0:
                    if delta_taint.GetFlags("modif_f") != None:
                        for flag in delta_taint.GetFlags("modif_f"):
                            if flags_to_check.has_key(flag):
                                flags_to_check[flag] = False
                                flags_todo -= 1
                                
                                if debug and debug_detailed:
                                    print ">DeadCodeElimination:ReduceBB - FOUND MODIF FLAG: adding False"
                    
                    if delta_taint.GetFlags("test_f") != None:
                        for flag in delta_taint.GetFlags("test_f"):
                            if flags_to_check.has_key(flag):
                                flags_to_check[flag] = True
                                flags_todo = 0
                                
                                if debug and debug_detailed:
                                    print ">DeadCodeElimination:ReduceBB - FOUND TESTF FLAG: adding True"
                                
                                break
                
                if regs_todo > 0:
                    
                    for op in delta_taint.GetDstTaints():
                        if op['type'] == 1:
                            regs = taint.GetExOpndRegisters(op['opnd'])
                            
                            for reg in regs:
                                if regs_to_check.has_key(reg[0]) and regs_to_check[reg[0]] <= reg[1]:
                                    regs_to_check[reg[0]] = False
                                    
                                    if debug and debug_detailed:
                                        print ">DeadCodeElimination:ReduceBB - FOUND DSTtaint False", reg
                                    
                                    regs_todo -= 1
                                    
                        elif op['type'] == 3 or op['type'] == 4:
                            regs = taint.GetExOpndRegisters(op['opnd'])
                            
                            for reg in regs:
                                if regs_to_check.has_key(reg[0]) and regs_to_check[reg[0]] <= reg[1]:
                                    regs_to_check[reg[0]] = True
                                    regs_todo = 0
                                    
                                    if debug and debug_detailed:
                                        print ">DeadCodeElimination:ReduceBB - FOUND DSTtaint True", reg[0]
                                    
                                    break
                    
                    for op in delta_taint.GetSrcTaints():
                        if op['type'] != None:
                            regs = taint.GetExOpndRegisters(op['opnd'])
                            
                            for reg in regs:
                                if regs_to_check.has_key(reg[0]) and regs_to_check[reg[0]] <= reg[1]:
                                    regs_to_check[reg[0]] = True
                                    regs_todo = 0
                                    
                                    if debug and debug_detailed:
                                        print ">DeadCodeElimination:ReduceBB - FOUND SRCtaint True", reg[0]
                                    
                                    break
                        else:
                            if debug and debug_detailed:
                                print ">DeadCodeElimination:ReduceBB - SRC# [%s:None]" % (op['opnd'])
                            raise MiscError
                            
                        
                if regs_todo == 0 and flags_todo == 0:
                    break
                    
            if regs_todo != 0 or flags_todo != 0:
                #let it live
                continue
            
            else:
                remove = 0
                for key in regs_to_check.iterkeys():
                    if regs_to_check[key] == True:
                        remove += 1
                        break
                
                for key in flags_to_check.iterkeys():
                    if flags_to_check[key] == True:
                        remove += 1
                        break
                
                if remove == 0:
                    #removing instruction
                    if debug:
                        print ">DeadCodeElimination:ReduceBB - Adding instruction to removal queue [%s] @ [%08x]" % (instr.GetDisasm(), instr.GetOriginEA())
                    
                    remove_todo.append(instr.GetOriginEA())
                    
        for item in remove_todo:
            if debug:
                print ">DeadCodeElimination:ReduceBB - REMOVING INSTRUCTION @[%08x]" % (item)
            self.function.RemoveInstruction(item)
            
        if len(remove_todo) > 0:
            return True
        else:
            return False
            
    def OptimizeFunction(self, function=None):
        if function:
            self.function = function
        
        modified = False
        for bb_ea in self.function.DFSFalseTraverseBlocks():
            if debug:
                print ">DeadCodeElimination:OptimizeFunction - DeadCode @ block [%08x]" % bb_ea
                
            modified |= self.ReduceBB(self.function.GetBBInstructions(bb_ea))
            
        return modified

class PeepHole:
    """Predefined optimization rules"""
    
    def __init__(self, function):
        self.function = function
            
    
    def RET2JMP(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
        
        if len(bb) < 1:
            return False
        
        instr = bb[-1]
        modified = False
        
        if instr.GetMnem().lower().find("ret") >= 0:
            for (ref, path) in self.function.GetRefsFrom(instr.GetOriginEA()):
                if ref != None:
                    if debug:
                        print ">PeepHole:RET2JMP - Found fake RET @ [%08x]" % instr.GetOriginEA()
                        print ">PeepHole:RET2JMP - Replacing RET with [JMP %08xh]" % ref
                    
                    instr.SetMnem("jmp")
                    instr.SetComment("-replaced[RET]")
                    instr.SetDisasm("jmp %08xh" % ref)
                    instr.SetOpcode('\xeb\xef')
                    instr.SetIsModified(True)
                    
                    find_push = bb[-2]
                    if find_push.GetMnem().lower() == "push":
                        self.function.RemoveInstruction(find_push.GetOriginEA(), bb[0].GetOriginEA())
                        #for testing, upper one is faster :)
                        #self.function.RemoveInstruction(find_push.GetOriginEA())
                        
                        modified = True
                        
                        if debug:
                            print "RET2JMP: Removig PUSH from "
                            
        return modified
    
    def SymetricNOP(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
            
        if len(bb) < 1:
            return False
        
        bb_len = len(bb)
        to_remove = []
        
        modified = False
        
        for offset in xrange(0, bb_len-1):
            mnem = bb[offset].GetMnem().lower()
            if mnem in ["mov", "xchg"]:
                instr = bb[offset]
                if instr.GetOpnd(1) == instr.GetOpnd(2):
                    if debug:
                        print ">PeepHole:SymetricNOP - Removing SYMETRIC @ [%08x] [%s] [%s %s]" % (instr.GetOriginEA(), instr.GetMnem(), instr.GetOpnd(1), instr.GetOpnd(2))
                    
                    instr.SetDisasm("NOP")
                    
                    instr.SetMnem("NOP")
                    instr.SetOpcode('\x90')
                    instr.SetOpnd(None, 1)
                    instr.SetOpnd(None, 2)
                    modified = True
                
        return modified

    def Shifts(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
            
        if len(bb) < 1:
            return False
        
        bb_len = len(bb)
        to_remove = []
        
        modified = False
        
        for offset in xrange(0, bb_len-1):
            mnem = bb[offset].GetMnem().lower()
            if mnem in ["shr", "shl", "sar", "sal"]:
                instr = bb[offset]
                if instr.GetOpndType(2) == 5:
                    shift = instr.GetOpndValue(2)
                    real_shift = shift & 0x1f
                    
                    if real_shift == 0:
                        if debug:
                            print ">PeepHole:Shifts - Removing nop shift instr @ [%08x] [%s] [%s %s]" % (instr.GetOriginEA(), instr.GetMnem(), instr.GetOpnd(1), instr.GetOpnd(2))
                    
                        instr.SetDisasm("NOP")
                    
                        instr.SetMnem("NOP")
                        instr.SetOpcode('\x90')
                        instr.SetOpnd(None, 1)
                        instr.SetOpnd(None, 2)
                        modified = True
                        
                    elif real_shift != shift:
                        if debug:
                            print ">PeepHole:Shifts - Modifying shift argument instr @ [%08x] [%s] [%s %s] -> [%s %s]" % (instr.GetOriginEA(), instr.GetMnem(), instr.GetOpnd(1), instr.GetOpnd(2), instr.GetOpnd(1), hex(real_shift))
                        
                        instr.SetOpnd(hex(real_shift), 2)
                        instr.SetOpndValue(real_shift, 2)
                        modified = True
                
        return modified

    def PUSHPOP(self, bb):
        if type(bb).__name__ == "generator":
            bb = list(bb)
            
        if len(bb) < 1:
            return False
        
        bb_len = len(bb)
        to_remove = []
        
        for offset in xrange(0, bb_len-1):
            mnem = bb[offset].GetMnem().lower()
            if mnem == "push":
                push = bb[offset]
                push_type = push.GetOpndType(1)
                
                if bb[offset+1].GetMnem() == "pop":
                    if debug:
                        print ">PeepHole:PUSHPOP - Removing PUSHPOP @ [%08x] [%s]" % (bb[offset].GetOriginEA(), bb[offset].GetMnem())
                    
                    pop = bb[offset+1]
                    
                    if push_type in [2,3,4] and pop.GetOpndType(1) in [2,3,4]:
                        continue
                    
                    to_remove.append(push.GetOriginEA())
                    
                    if push_type == 2:
                        pop.SetDisasm("MOV %s, [%09xh]" % (pop.GetOpnd(1), push.GetOpndValue(1)))
                    else:
                        pop.SetDisasm("MOV %s, %s" % (pop.GetOpnd(1), push.GetOpnd(1)))
                    
                    pop.SetMnem("MOV")
                    pop.SetOpnd(pop.GetOpnd(1), 1)
                    pop.SetOpnd(push.GetOpnd(1), 2)
                    
                    pop.SetOpcode(Assembler.SimpleAsm(pop.GetDisasm()))
                    pop.SetOpndType(push.GetOpndType(1), 2)
                    pop.SetOpndValue(push.GetOpndValue(1), 2)
                    
                    pop.SetOpcode('\xba\x85')
                
                else:
                    for ins in bb[offset+1:]:
                        if ins.GetMnem() == "pop":
                            if debug:
                                print ">PeepHole:PUSHPOP - Removing PUSHPOP @ [%08x] [%s]" % (bb[offset].GetOriginEA(), bb[offset].GetMnem())
                            
                            pop = ins
                            
                            if push.GetOpndType(1) in [2,3,4] and pop.GetOpndType(1) in [2,3,4]:
                                break
                            
                            to_remove.append(push.GetOriginEA())
                            
                            if push_type == 2:
                                pop.SetDisasm("MOV %s, [%09xh]" % (pop.GetOpnd(1), push.GetOpndValue(1)))
                            else:
                                pop.SetDisasm("MOV %s, %s" % (pop.GetOpnd(1), push.GetOpnd(1)))
                            
                            pop.SetMnem("MOV")
                            pop.SetOpnd(pop.GetOpnd(1), 1)
                            pop.SetOpnd(push.GetOpnd(1), 2)
                            
                            pop.SetOpcode(Assembler.SimpleAsm(pop.GetDisasm()))
                            pop.SetOpndType(push.GetOpndType(1), 2)
                            pop.SetOpndValue(push.GetOpndValue(1), 2)
                            
                            pop.SetOpcode('\xba\x85')
                            
                            break
                        
                        taint = ins.GetTaintInfo()
                        
                        skip_this = 0
                        for op in taint.GetDstTaints():
                            if op['type'] == 1:
                                reg = taint.GetExOpndRegisters(op['opnd'])
                                if len(reg) != 1:
                                    if debug and debug_detailed:
                                        print ">PeepHole:PUSHPOP - !GetExOpndRegisters returned suspicious data"
                                        print ">PeepHole:PUSHPOP - ", op['opnd']
                                        print ">PeepHole:PUSHPOP - ", reg
                                        skip_this = 1
                                        break
                                
                                if reg[0][0] == "ESP":
                                    skip_this = 1
                                    break
                                
                                elif push_type == 1 and reg[0][0] == push.GetOpnd(1).upper():
                                    skip_this = 1
                                    break
                                
                            elif push_type in [2,3,4] and op['type'] in [2,3,4]:
                                skip_this = 1
                                break
                                
                        if skip_this == 1:
                            break
                            
                        
                        skip_this = 0
                        for op in taint.GetSrcTaints():
                            if op['type'] == 1:
                                reg = taint.GetExOpndRegisters(op['opnd'])
                                if len(reg) != 1:
                                    if debug and debug_detailed:
                                        print ">PeepHole:PUSHPOP - !GetExOpndRegisters returned suspicious data"
                                        print ">PeepHole:PUSHPOP - ", op['opnd']
                                        print ">PeepHole:PUSHPOP - ", reg
                                        skip_this = 1
                                        break
                                
                                if reg[0][0] == "ESP":
                                    skip_this = 1
                                    break
                                
                        if skip_this == 1:
                            break
                        
                    if skip_this == 1:
                        skip_this = 0
                        continue
        
        for item in to_remove:
            self.function.RemoveInstruction(item)
        
        if len(to_remove) > 0:
            return True
        else:
            return False
        
    def ReduceBB(self, bb):
        optimization_order = ['PUSHPOP', 'RET2JMP', 'SymetricNOP', 'Shifts']
        #optimization_order = ['RET2JMP']
        
        modified = False
        for optimization in optimization_order:
            modified |= getattr(self, optimization)(bb)
            
        return modified

    
    def OptimizeFunction(self, function=None):
        if function:
            self.function = function
        
        modified = False
        for bb_ea in self.function.DFSFalseTraverseBlocks():
            modified |= self.ReduceBB(list(self.function.GetBBInstructions(bb_ea)))
            
        return modified
