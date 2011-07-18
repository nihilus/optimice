'''
    Block tainting class
'''

import pickle
import zlib
import re

'''
    o_void = 0
    o_reg = 1
    o_mem = 2
    o_phrase = 3
    o_displ = 4
    o_imm = 5
    o_far = 6
    o_near = 7
    o_idpspec0 = 8
    o_idpspec1 = 9
    o_idpspec2 = 10
    o_idpspec3 = 11
    o_idpspec4 = 12
    o_idpspec5 = 13
    o_custom = 20
'''

#EAX,AX,AH,AL,EBX,BX,BH,BL,ECX,CX,CH,CL,EDX,DX,DH,DL,ESI,SI,EDI,DI,EBP,BP,ESP,SP

debug = 0

class TaintInstr:
    """ """
    
    def __init__(self):
        self.ea = None
        self.src = []
        self.dst = []
        self.flags = {}
        self.hidden = None
        
        #for easier debugging
        self.mnem = None
        
        self.reg2ereg = {"RAX":"EAX", "AL":"EAX", "AH":"EAX", "AX":"EAX", "EAX":"EAX", "RBX":"EBX", "BL":"EBX", "BH":"EBX", "BX":"EBX", "EBX":"EBX", "RCX":"EAX", "CL":"ECX", "CH":"ECX", "CX":"ECX", "ECX":"ECX", "RDX":"EDX", "DL":"EDX", "DH":"EDX", "DX":"EDX", "EDX":"EDX", "RSI":"ESI", "ESI":"ESI", "SI":"ESI", "RDI":"EDI", "EDI":"EDI", "DI":"EDI", "RBP":"EBP", "EBP":"EBP", "BP":"EBP", "RSP":"ESP", "ESP":"ESP", "SP":"ESP", "ES":"ES", "SS":"SS"}
    
    def GetRegPos(self, reg):
        '''[4rax[3eax[2ax[1ah|0al]]]] | -1'''
        
        reg = reg.lower()
        if len(reg) == 3:
            if reg[0] == 'r':
                return 4
            elif reg[0] == 'e':
                return 3
            else:
                return -1
        elif len(reg) == 2:
            if reg[1] == 'x':
                return 2
            elif reg[1] == 'h':
                return 1
            elif reg[1] == 'l':
                return 0
            else:
                return -1
        else:
            return -1
    
    def SetOriginEA(self, ea):
        self.ea = ea
        
    def GetOriginEA(self):
        return self.ea
    
    def AddSrcTaint(self, src):
        if src['type'] == None:
            if src['opnd'] == "SS:[rSP]":
                src['opnd'] = "[ESP]"
                src['type'] = 3
            else:
                src['type'] = self.GuessOpType(src['opnd'])
                
                if debug:
                    print ">TaintInstr:AddSrcTaint - Adding [%d] type for [%s]" % (src['type'], src['opnd'])
                #raise MiscError
        
        #if debug:
            #print ">TaintInstr:AddSrcTaint - EXPANDED OPND: [%s] #-># " % src['opnd'], self.GetExOpndRegisters(src['opnd'])
            
        src['opnd'] = src['opnd'].upper()
        self.src.append(src)
        
    def GetSrcTaints(self):
        return self.src
    
    def AddDstTaint(self, dst):
        if debug:
            print dst
        
        if dst['type'] == None:
            if dst['opnd'] == "SS:[rSP]":
                dst['opnd'] = "[ESP]"
                dst['type'] = 3
            else:
                dst['type'] = self.GuessOpType(dst['opnd'])
                
                if debug:
                    print ">TaintInstr:AddDstTaint - Adding [%d] type for [%s]" % (dst['type'], dst['opnd'])
                #raise MiscError
        
        dst['opnd'] = dst['opnd'].upper()
        self.dst.append(dst)
        
    def GetDstTaints(self):
        return self.dst
    
    def GuessOpType(self, op):
        op = op.upper()
        if self.reg2ereg.has_key(op):
            return 1
        
        elif op.find("[") >= 0:
            if op.find("+") >= 0 or op.find("-") >= 0 or op.find("*") >= 0:
                return 4
            else:
                clean_op = re.search(r"\[(.*?)\]", op).group(1).strip()
                if self.reg2ereg.has_key(clean_op):
                    return 3
                elif re.match(r"\d+", op).group().strip() != None:
                    return 2
                else:
                    if debug:
                        print ">TaintInstr:GuessOpType - GuessOpType FAILED!!"
                        print ">TaintInstr:GuessOpType - op:", op
                    
                    return 20
                    #raise MiscError
                
        elif op.lower().find("flags") >= 0:
            if debug:
                print ">TaintInstr:GuessOpType - FLAGS DETECTED: TO_RESOLVE, returning 0"
            return 0
        else:
            if debug:
                print ">TaintInstr:GuessOpType - GuessOpType FAILED!!"
                print ">TaintInstr:GuessOpType - op:", op
            
            return 20
            #raise MiscError
        
    def SetFlags(self, flags):
        self.flags = flags
        
    def GetFlags(self, what=None):
        if what != None:
            if self.flags.has_key(what):
                return self.flags[what]
            else:
                return None
        else:
            return self.flags
        
    def GetOpndRegisters(self, opnd):
        if debug:
            print ">TaintInstr:GetOpndRegisters - ", opnd
            
        opnd = opnd.upper()
        opnd = re.sub(r"(SHORT|NEAR|FAR|PTR|QWORD|DWORD|WORD|TBYTE|BYTE)", " ", opnd).strip()
        opnd = re.sub(r"(?:CS|SS|DS|ES(?:\s|:|\+|\-|\*)|FS|GS)", " ", opnd).strip()
        opnd = opnd.replace(":"," ").replace("["," ").replace("]"," ").replace("+"," ")
        
        opnd = re.sub(r"\s+", " ", opnd).strip()
        ops = opnd.upper().split(" ")
        
        if debug:
            print ">TaintInstr:GetOpndRegisters - Result: ", ops
        
        return ops
    
    def GetExOpndRegisters(self, opnd):
        ops = self.GetOpndRegisters(opnd)
        regs = []
        
        for op in ops:
            if self.reg2ereg.has_key(op):
                regs.append( (self.reg2ereg[op], self.GetRegPos(op)) )
            else:
                if debug:
                    print ">TaintInstr:GetExOpndRegisters - #REG2EREG# No mapping for [%s]" % op
                pass
        
        return regs
    
    def TestFunction(self, function):
        for bb_ea in function.DFSFalseTraverseBlocks():
            for instr in function.GetBBInstructions(bb_ea):
                self.CalculateInstructionTaint(instr)
                