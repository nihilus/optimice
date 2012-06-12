'''
    Instruction representation class
    
self.instr = {
    'origin_ea' : 0,
    'opcode' : 0,
    'mnem' : '',
    'disasm' : '',
    'op1' : '',
    'op1_type' : '',
    'op1_val' : 0,
    'op2' : '',
    'op2_type' : '',
    'op2_val' : 0,
    'call_addr' : 0,
    'modified' : 0,
    'comment' : '',
}
'''

import idc
import idautils
import idaapi

import re
import zlib
import pickle
import os

import BlockTainting

debug = 0

jcc = {'ja':True, 'jae':True, 'jb':True, 'jbe':True, 'jc':True, 'jcxz':True, 'jecxz':True, 'je':True, 'jg':True, 'jge':True, 'jl':True, 'jle':True, 'jna':True, 'jnae':True, 'jnb':True, 'jnbe':True, 'jnc':True, 'jne':True, 'jng':True, 'jnge':True, 'jnl':True, 'jnle':True, 'jno':True, 'jnp':True, 'jns':True, 'jnz':True, 'jo':True, 'jp':True, 'jpe':True, 'jpo':True, 'js':True, 'jz':True}

#This will point instructionsDICT.data which is preprocessed
#MazeGen's http://ref.x86asm.net/x86reference.xml in a python dict
x86InstructionData = None

class Instruction:
    """Representing Instruction information and interfaces"""
    def __init__(self, ea=None):
        self.instr = {}
        self.prefix = None
        self.mnem = None
        self.op = {}
        
        self.taintInfo = None
        self.t_prefix = None
        self.t_mnem = None
        self.t_op = {}
        self.group = None
        
        self.taint = None
        
        if ea != None:
            self.SetOriginEA(ea)

    def LoadInstructionData(self):
        global x86InstructionData
        
        if x86InstructionData == None:
            path = os.path.realpath(__file__)
            path = path[:path.rfind(os.path.sep)+1] + "instructionsDICT.data"
            print path
            
            if path == "":
                print 
                path = idaapi.askfile_c(1, "instructionsDICT.data", "Go to optimice dir and select instructionsDICT file")
                
            fp = open(path, "rb")
            data = fp.read()
            
            x86InstructionData = pickle.loads(zlib.decompress(data))
            fp.close()

    def GetTypeGroup(self, group=None):
        if self.taint == None:
            self.LoadInstructionData()
            self.taint = self.CalculateInstructionTaint()
        
        if group != None:
            if self.group.has_key(group):
                return self.group[group]
            else:
                return None
        else:
            return self.group

    def GetTaintInfo(self):
        if self.taint != None:
            return self.taint
        
        self.LoadInstructionData()
        
        self.taint = self.CalculateInstructionTaint()
        return self.taint

    def PopulateInfoFromDisasm(self):
        #NOTE: (Set/Get)Opnd(1,1) CAN be used insead of (Set/Get)Opnd(2,1) when first operand is empty
        # that is the case for FSTP instruction (and like) where IDA skips first argument and populates
        # only second. This should be handeled explicitly so we dont break tainting.
        
        disas = self.GetDisasm().upper().strip()
        disas = re.sub(r";.*","", disas, 1).strip()
        prefix = re.match(r"((?:LOCK |REPNE |REPNZ |REP |REPE |REPZ |CS(?:\s|:)|SS(?:\s|:)|DS(?:\s|:)|ES(?:\s|:)|FS(?:\s|:)|GS(?:\s|:))*)", disas).group()
        prefix = prefix.strip().strip(":")
        disas = re.sub(r"(?:LOCK |REPNE |REPNZ |REP |REPE |REPZ |CS(?:\s|:)|SS(?:\s|:)|DS(?:\s|:)|ES(?:\s|:)|FS(?:\s|:)|GS(?:\s|:))*", "", disas, 1).strip()
        mnem = re.match(r"\w+", disas).group().strip()
        disas = re.sub(r"\w+", "", disas, 1).strip()
        ops = [x.strip() for x in disas.split(",")]
        
        if debug:
            print ">Instruction:PopulateInfoFromDisasm - ", self.GetDisasm()
            print ">Instruction:PopulateInfoFromDisasm - prefix[%s] mnem[%s] ops[%s]" % (prefix, mnem, ';'.join(ops))
        
        self.SetMnemPrefix(prefix, 1)
        self.SetMnem(mnem, 1)
        
        for x in xrange(0,len(ops)):
            if len(ops[x]) > 0:
                #self.op[x] = ops[x]
                self.SetOpnd(ops[x], x+1, 1)
            else:
                pass
                #raise MiscError
        
    def GetMnemPrefix(self, type=0):
        if type == 0:
            return self.prefix
        elif type == 1:
            return self.t_prefix
        else:
            raise MiscError
        
    def SetMnemPrefix(self, prefix, type=0):
        if type == 0:
            self.prefix = prefix
        elif type == 1:
            self.t_prefix = prefix
        else:
            raise MiscError
        
        self.taint = None

    def SetOriginEA(self, ea):
        self.instr['origin_ea'] = ea
        
    def GetOriginEA(self):
        if self.instr.has_key('origin_ea'):
            return self.instr['origin_ea']
        else:
            return None

    def IsJcc(self):
        if jcc.has_key(self.GetMnem().lower()):
            return True
        else:
            return False
        
    def IsCall(self):
        if self.GetMnem().lower().find("call") >= 0:
            return True
        else:
            return False
        
    def IsRet(self):
        if self.GetMnem().lower().find("ret") >= 0:
            return True
        else:
            return False
        
    def IsJmp(self):
        if self.GetMnem().lower().find("jmp") >= 0:
            return True
        else:
            return False
        
    def IsLoop(self):
        if self.GetMnem().lower().find("loop") >= 0:
            return True
        else:
            return False
        
    def IsCFI(self):
        if self.IsJcc():
            return True
        elif self.IsJmp():
            return True
        elif self.IsCall():
            return True
        elif self.IsRet():
            return True
        elif self.IsLoop():
            return True
        else:
            return False

    def SetOpcode(self, opcode):
        self.instr['opcode'] = opcode
        
        self.taint = None
        
    def GetOpcode(self):
        if self.instr.has_key('opcode'):
            return self.instr['opcode']
        else:
            return None


    def SetMnem(self, mnem, type=0):
        if type == 0:
            self.instr['mnem'] = mnem
        elif type == 1:
            self.t_mnem = mnem
        else:
            raise MiscError
        
        self.taint = None
        
    def GetMnem(self, type=0):
        if type == 0:
            if self.instr.has_key('mnem'):
                return self.instr['mnem']
            else:
                return None
        elif type == 1:
            if self.t_mnem != None:
                return self.t_mnem
            else:
                return None


    def SetComment(self, comment):
        self.instr['comment'] = comment
        
    def GetComment(self):
        if self.instr.has_key('comment'):
            return self.instr['comment']
        else:
            return None

    def SetDisasm(self, disasm):
        disasm = disasm.replace("ht ", "")
        self.instr['disasm'] = disasm
        
        self.taint = None
        
    def GetDisasm(self):
        if self.instr.has_key('disasm'):
            return self.instr['disasm']
        else:
            return None

    #Normalized disasm for sym_exec
    def GetNDisasm(self):
        if self.instr.has_key('disasm'):
            dis = self.instr['disasm'].lower()
            dis = re.sub(r"([\dabcdef]+)h", r"0x\1", dis)
            return dis
        else:
            return None

    def SetIsModified(self, modified):
        self.instr['modified'] = modified
        
    def GetIsModified(self):
        if self.instr.has_key('modified'):
            return self.instr['modified']
        else:
            return None

    def SetOpnd(self, op, opnr, type=0):
        if op != None:
            op = re.sub(r"(^|\s)ST($|\s)", "ST0", op.upper())
        
        op_name = 'op%d' % opnr
        if type == 0:
            if op != '':
                self.instr[op_name] = op
        elif type == 1:
            if op != '':
                self.t_op[op_name] = op
                
        self.taint = None
            
    def GetOpnd(self, opnr, type=0):
        op_name = 'op%d' % opnr
        
        if type == 0:
            if self.instr.has_key(op_name):
                return self.instr[op_name]
            else:
                return None
        elif type == 1:
            if self.t_op.has_key(op_name):
                return self.t_op[op_name]
            else:
                return None
    
    def SetOpndType(self, op_type, opnr):
        op_name = 'op%d_type' % opnr
        self.instr[op_name] = op_type
        
        self.taint = None
        
    def GetOpndType(self, opnr):
        op_name = 'op%d_type' % opnr
        if self.instr.has_key(op_name):
            return self.instr[op_name]
        else:
            return None
    
    def SetOpndSize(self, op_size, opnr):
        op_name = 'op%d_size' % opnr
        self.instr[op_name] = op_size
        
    def GetOpndSize(self, opnr):
        op_name = 'op%d_size' % opnr
        if self.instr.has_key(op_name):
            return self.instr[op_name]
        else:
            return None
    
    def GetOpndPrefixSize(self, opnr):
        op = self.GetOpndPrefix(opnr)
        if op != None:
            op = op.upper()
            if op == "BYTE":
                return 1
            elif op == "DWORD":
                return 4
            elif op == "WORD":
                return 2
            elif op == "QWORD":
                return 8
            elif op == "TBYTE":
                return 10
            else:
                print "Unknown SIZE = [%s]!" % op
                return None
        else:
            return None
        
    def StripOpndPrefix(self, opnd):
        clean = re.sub(r"\s*([A-Z]+)\s+PTR\s*", " ", opnd.upper())
        return clean
    
    def GetOpndPrefix(self, opnr):
        #NOTE: SHOULD DEFINE EXACTLY WHAT IS THIS SUPPOSED TO RETURN
        disas = self.GetDisasm().upper()
        
        if opnr == 1:
            if disas.find("PTR") >= 0:
                prefix = re.search(r"\s+([A-Z]+)\s+PTR\s+", disas)
                if prefix != None:
                    return prefix.group(1)
                else:
                    return None
            else:
                prefix = re.search(r".*?(BYTE|DWORD|QWORD|WORD)\s.*?,?", disas)
                if prefix != None:
                    return prefix.group(1)
                else:
                    return None
        else:
            result = re.search(r"(?:.*?,){%d}([^,]*)" % (opnr-1), disas)
            
            if result != None:
                result = result.group(1)
                if result.find("PTR") >= 0:
                    prefix = re.search(r"\s+([A-Z]+)\s+PTR\s+", result)
                    if prefix != None:
                        return prefix.group(1)
                    else:
                        return None
            
        return None
        
    def SetOpndValue(self, op_val, opnr):
        op_name = 'op%d_val' % opnr
        self.instr[op_name] = op_val
        
        self.taint = None
        
    def GetOpndValue(self, opnr):
        op_name = 'op%d_val' % opnr
        if self.instr.has_key(op_name):
            return self.instr[op_name]
        else:
            return None
        
    def SetCallAddr(self, call_addr):
        self.instr['call_addr'] = call_addr
        
    def GetCallAddr(self):
        if self.instr.has_key('call_addr'):
            return self.instr['call_addr']
        else:
            return None
        
    def GetRegSize(self, reg):
        '''[8rax[4eax[2ax[1ah|1al]]]] | 0'''
        
        reg = reg.lower()
        if len(reg) == 3:
            if reg[0] == 'r':
                return 8
            elif reg[0] == 'e':
                return 4
            else:
                return -1
        elif len(reg) == 2:
            if reg[1] == 'x':
                return 2
            elif reg[1] == 'h':
                return 1
            elif reg[1] == 'l':
                return 1
            else:
                return 0
        else:
            return 0
        
    def BytesToPrefix(self, size):
        if size == 1:
            prefix = "byte"
        elif size == 2:
            prefix = "word"
        elif size == 4:
            prefix = "dword"
        elif size == 8:
            prefix = "qword"
        elif size == 10:
            prefix = "tword"
        else:
            prefix = ""
        
        return prefix
    
    def CalculateInstructionTaint(self):
        taint = BlockTainting.TaintInstr()
        taint.SetOriginEA(self.GetOriginEA())
        
        global x86InstructionData
        
        self.PopulateInfoFromDisasm()
        
        disasm = self.GetDisasm().upper()
        mnems = [x.upper().strip() for x in self.GetMnemPrefix(1).split(" ") if x!='']
        mnems.append(self.GetMnem(1).upper().strip())
        
        if len(mnems) < 1:
            print ">BlockTainting:CalculateInstructionTaint - ERROR: No menmonics for instruction!"
            print ">BlockTainting:CalculateInstructionTaint - Disam:", disasm
            raise MiscError
        
        if debug:
            instr_string = ' '.join(mnems)
            if self.GetOpnd(1, 1) != None:
                #print ">BlockTainting:CalculateInstructionTaint - op1[%s];type[%d]" % (self.GetOpnd(1, 1), self.GetOpndType(1, 1))
                instr_string += " " + self.GetOpnd(1, 1)
                
            if self.GetOpnd(2, 1) != None:
                #print ">BlockTainting:CalculateInstructionTaint - op2[%s];type[%d]" % (self.GetOpnd(2, 1), self.GetOpndType(2, 1))
                instr_string += ", " + self.GetOpnd(2, 1)
                
            print ">BlockTainting:CalculateInstructionTaint - [%s] [%08x]" % (instr_string, self.GetOriginEA())
            print ">BlockTainting:CalculateInstructionTaint - Mnems", mnems
        
            print ">BlockTainting:CalculateInstructionTaint - OriginEA=[%08x] Disasm[%s] Mnems[%s]" % (self.GetOriginEA(), disasm, ' '.join(mnems))
        
        taint.mnem = ' '.join(mnems)
        
        for mnem in mnems:
            if mnem == 'XLAT':
                mnem = 'XLATB'
            elif mnem == 'PUSHFW' or mnem == 'POPFW':
                mnem = mnem.replace('FW', 'F')
                
            if not x86InstructionData.has_key(mnem):
                print "NOTE: INSTRUCTION NOT RECOGNIZED [%s] @ [%08x] [%s]" % (mnem, self.GetOriginEA(), mnems)
                print self.GetMnem(1)
                print list(self.GetMnemPrefix(1))
            
            opcode = self.GetOpcode()
            for opc in opcode:
                op = '%02x' % ord(opc)
                op = unicode(op.upper())
                if x86InstructionData[mnem].has_key(op):
                    info = x86InstructionData[mnem][op]
                    
                    # Load instruction group information
                    if info[0].has_key('grp'):
                        self.group = info[0]['grp']
                    
                    if debug:
                        print ">BlockTainting:CalculateInstructionTaint - Disasm:", disasm
                        #check for situation that mnem has more elements
                        #check that [0] is really x32 self
                        if False and len(info) > 1:
                            print ">BlockTainting:CalculateInstructionTaint - WARRNING: More than one entry:", mnem, info
                            
                    if info[0].has_key('ring'):
                        if info[0]['ring'] != '3' and info[0]['ring'] != 'f':
                            print ">BlockTainting:CalculateInstructionTaint - WARRNING: Instruction [%s] Ring != 3!" % taint.mnem
                      
                    if debug:  
                        if info[0]['flags'].has_key('f_vals'):
                            print ">BlockTainting:CalculateInstructionTaint - ", mnem, info[0]['flags']['f_vals']
                        print ">BlockTainting:CalculateInstructionTaint - Flags", info[0]['flags']
                    
                    taint.SetFlags(info[0]['flags'])
                    
                    op_counter = 1
                    for operand in info[0]['operands']:
                        if operand.has_key("address") and operand["address"] == "SC":
                            if debug:
                                print ">BlockTainting:CalculateInstructionTaint - <<SC>> Adding ESP"
                                
                            ins = {}
                            ins['passive'] = True
                            ins['type'] = 1
                            ins['value'] = None 
                            ins['opnd'] = "ESP"
                            taint.AddDstTaint(ins)
                            
                        elif operand.has_key("address") and operand["address"] == "F":
                            if operand['opType'] == 'dst':
                                fflags = {'def_f':u'odiszapc'}
                            else:
                                fflags = {'test_f':u'odiszapc'}
                            taint.SetFlags(fflags)
                            
                        if operand.has_key('displayed'):
                            if operand['opType'] == 'src':
                                ins = {}
                                ins['passive'] = True
                                ins['type'] = None #self.GetOpndType(op_counter)
                                ins['value'] = None #self.GetOpndValue(op_counter)
                                ins['opnd'] = operand['data'] #self.GetOpnd(op_counter)
                                
                                try:
                                    taint.AddSrcTaint(ins)
                                except:
                                    print ">BlockTainting:CalculateInstructionTaint - Exception @ %08x" % self.GetOriginEA()
                                
                                if debug:
                                    print ">BlockTainting:CalculateInstructionTaint - src[hid]->",
                                    
                            elif operand['opType'] == 'dst':
                                ins = {}
                                ins['passive'] = True
                                ins['type'] = None #self.GetOpndType(op_counter)
                                ins['value'] = None #self.GetOpndValue(op_counter)
                                ins['opnd'] = operand['data'] #self.GetOpnd(op_counter)
                                
                                try:
                                    taint.AddDstTaint(ins)
                                except:
                                    print ">BlockTainting:CalculateInstructionTaint - Exception @ %08x" % self.GetOriginEA()
                                
                                if (not operand.has_key('depend')) or operand['depend'] != "no":
                                    try:
                                        taint.AddSrcTaint(ins)
                                    except:
                                        print ">BlockTainting:CalculateInstructionTaint - Exception @ %08x" % self.GetOriginEA()
                                
                                if debug:
                                    print ">BlockTainting:CalculateInstructionTaint - dst[hid]->",
                                    
                            else:
                                print ">BlockTainting:CalculateInstructionTaint - ERROR!"
                                raise MiscError
                                
                            if debug:
                                print ">BlockTainting:CalculateInstructionTaint - ", ins['passive'], ins['type'], ins['value'], ins['opnd']
                                #print operand.get('data', None), operand.get('address', None), operand.get('depends')
                            
                        else:
                            if operand['opType'] == 'src':
                                if self.GetOpndType(op_counter) != -1 and self.GetOpndType(op_counter) != None:
                                    if self.GetOpnd(op_counter, 1) != None:
                                        ins = {}
                                        ins['passive'] = False
                                        ins['type'] = self.GetOpndType(op_counter)
                                        ins['value'] = self.GetOpndValue(op_counter)
                                        ins['opnd'] = self.GetOpnd(op_counter, 1)
                                        
                                        try:
                                            taint.AddSrcTaint(ins)
                                        except:
                                            print ">BlockTainting:CalculateInstructionTaint - Exception @ %08x" % self.GetOriginEA()
                                        
                                        if debug:
                                            print ">BlockTainting:CalculateInstructionTaint - \tsrc->", ins['passive'], ins['type'], ins['value'], ins['opnd']
                                            #print self.GetOpnd(op_counter),"\t#src->", operand
                                    else:
                                        if mnem != "IMUL":
                                            print ">BlockTainting:CalculateInstructionTaint - GetOpnd", self.GetOpnd(op_counter, 1)
                                            print ">BlockTainting:CalculateInstructionTaint - GetOpndType", self.GetOpndType(op_counter)
                                            print ">BlockTainting:CalculateInstructionTaint - GetMnem", self.GetMnem()
                                            print ">BlockTainting:CalculateInstructionTaint - WARRNING: Operand HIDDEN!", "op_counter[%d] @ [%08x]" % (op_counter, self.GetOriginEA())
                                            raise MiscError
                                        
                                else:
                                    print ">BlockTainting:CalculateInstructionTaint - ERROR"
                                    print "This Error can be side effect of normal instructions that have no RefsFrom!"
                                    raise MiscError
                                    
                            elif operand['opType'] == 'dst':
                                if self.GetOpndType(op_counter) != -1 and self.GetOpndType(op_counter) != None:
                                    if self.GetOpnd(op_counter, 1) != None:
                                        ins = {}
                                        ins['passive'] = False
                                        ins['type'] = self.GetOpndType(op_counter)
                                        ins['value'] = self.GetOpndValue(op_counter)
                                        ins['opnd'] = self.GetOpnd(op_counter, 1)
                                        
                                        try:
                                            taint.AddDstTaint(ins)
                                        except:
                                            print ">BlockTainting:CalculateInstructionTaint - Exception @ %08x" % self.GetOriginEA()
                                
                                        if (not operand.has_key('depend')) or operand['depend'] != "no":
                                            #this is a depending register so it should be also in SrcTaint
                                            try:
                                                taint.AddSrcTaint(ins)
                                            except:
                                                print ">BlockTainting:CalculateInstructionTaint - Exception @ %08x" % self.GetOriginEA()
                                    
                                        if debug:
                                            print ">BlockTainting:CalculateInstructionTaint - \tdst->", ins['passive'], ins['type'], ins['value'], ins['opnd']
                                            #print self.GetOpnd(op_counter),"\t#dst->", operand
                                    else:
                                        print ">BlockTainting:CalculateInstructionTaint - WARRNING: Operand HIDDEN!", "op_counter[%d] @ [%08x]" % (op_counter, self.GetOriginEA())
                                        print ">BlockTainting:CalculateInstructionTaint - GetOpndType", self.GetOpndType(op_counter, 1)
                                        print ">BlockTainting:CalculateInstructionTaint - ", operand, self.GetOpnd(op_counter)
                                        print ">BlockTainting:CalculateInstructionTaint - GetMnem", self.GetMnem()
                                        raise MiscError
                                else:
                                    print ">BlockTainting:CalculateInstructionTaint - ERROR: op_counter[%d]" % (op_counter)
                                    raise MiscError
                                
                            op_counter += 1
                                
                    #instruction found, exit the loop
                    break
            
            else:
                if debug:
                    print ">BlockTainting:CalculateInstructionTaint - ERROR: NO KEY!"
                    print ">BlockTainting:CalculateInstructionTaint - mnem[%s] OriginEA[%08x]" % (mnem, self.GetOriginEA())
                    print ">BlockTainting:CalculateInstructionTaint - ", opc, ''.join(['%02x' % ord(opcode[x]) for x in xrange(0, len(opcode))])
                    print ">BlockTainting:CalculateInstructionTaint - ", x86InstructionData[mnem].keys()
                    raise MiscError
        
        return taint
