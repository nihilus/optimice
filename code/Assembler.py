'''
    Assembler class
'''
import subprocess
import copy
import array
import os
import re
import pickle
import zlib
import random

import idc
import idautils
import idaapi

debug = 0

class MiscError(Exception):
    def __init__(self):
        return
    
def SimpleAsm(string):
    idc.Batch(1)
    
    while True:
        seg_start = random.randint(0x1000, 0xffffffff)
        seg_size = 0x20
        if idc.SegCreate(seg_start, seg_start+seg_size, 0, 1, 0, 0) != 0:
            break
    
    tmp = idaapi.assemble(seg_start, 0, seg_start, 1, string)
    
    if tmp == 0:
        while idc.SegDelete(seg_start, 0) != 0: pass
        idc.Batch(0)
        print "Failed to assemble [%s]" % string
        raise MiscError
    
    idc.MakeCode(seg_start)
    
    opcode = ''.join([ chr(idc.Byte(seg_start+i)) for i in xrange(0, idc.ItemSize(seg_start)-1) ])
    
    while idc.SegDelete(seg_start, 0) != 0: pass
    
    idc.Batch(0)
    return opcode


def LoadSavedAssemblers(seg_ea=None):
    assemblers = {}
    
    opty_dir = idc.GetIdbPath()
    opty_dir = opty_dir[:opty_dir.rfind(os.sep)] + os.sep + "optimice_%s" % idc.GetInputFile() + os.sep
    if not os.path.isdir(opty_dir):
        return None
    
    if seg_ea == None:
        for fname in os.listdir(opty_dir):
            if re.match(r"Assembler_[0-9ABCDEF]+\.pickle.zlib", fname) != None:
                seg_ea = re.match(r"Assembler_([0-9ABCDEF]+)\.pickle.zlib", fname).group(1)
                fp = open(opty_dir + fname, "rb")
                asm = pickle.loads(zlib.decompress(fp.read()))
                fp.close()
                
                assemblers[seg_ea] = asm
    
    else:
        fname = "Assembler_%08x.pickle.zlib" % (seg_ea)
        
        try:
            fp = open(opty_dir + fname, "r")
            asm = pickle.loads(zlib.decompress(fp.read()))
            assemblers[seg_ea] = asm
            fp.close()
            
        except:
            return None
        
    return assemblers


class Assemble:
    """Assemble function code to arbitrary memory segment"""
    
    def __init__(self, segment_start=None, segment_size=None):
        self.segment_start = 0
        self.segment_size = 0
        self.segment_name = ''
        self.free_ea = 0
        self.jmp_deps = {}
        self.ref_instr = {}
        self.bb_head_ea = {}
        self.nasm = False
        self.nasm_path = ""
        self.opty_dir = None
        self.functions = {}
        self.jmp_table = ""
        self.jmp_table_refs = []
        
        self.AllocateCodeSegment()

    def SaveState(self):
        opty_dir = idc.GetIdbPath()
        opty_dir = opty_dir[:opty_dir.rfind(os.sep)] + os.sep + "optimice_%s" % idc.GetInputFile()
        if not os.path.isdir(opty_dir):
            os.mkdir(opty_dir)
        save_fname = "%s%sAssembler_%08x.pickle.zlib" % (opty_dir, os.sep, self.segment_start)
        
        fw = open(save_fname, "wb+")
        s1 = pickle.dumps(self)
        fw.write(zlib.compress(s1))
        fw.close()
        
        print ">Assembler:SaveState - File [%s] saved" % (save_fname)
    
    def NasmWriteToFile(self, string, instr=None):
        string = string.upper()
        
        string = re.sub(r"DS:DBL_([\dABCDEF]+)", r"QWORD [DS:0\1h]", string)
        string = re.sub(r"DS:FLT_([\dABCDEF]+)", r"DWORD [DS:0\1h]", string)
        
        string = re.sub(r"DS:(BYTE|DWORD|QWORD|WORD)_([\dABCDEF]+)", r"\1 [DS:0\2h]", string)
        string = re.sub(r"(BYTE|DWORD|QWORD|WORD)_([\dABCDEF]+)", r"\1 [0\2h]", string)
        
        string = string.replace("PTR ", "")
        string = string.replace("SETALC", "db 0xd6")
        string = string.replace("XMMWORD", "").replace("TBYTE ", "")
        
        string = re.sub(r"ST\((\d+)\)", r"ST\1", string)
        string = re.sub(r",\s*ST\s*$", r"", string)
        
        string = re.sub(r"(INS[BWD])\s+DX\s*", r"\1", string)
        string = re.sub(r"(OUT[BWD])\s+DX\s*", r"\1", string)
        
        string = re.sub(r"FNSAVE\s+BYTE\s+\[", r"FNSAVE [", string)
        
        string = re.sub(r"[^\[](FS|DS|ES|SS|CS|GS):\[?([^,\]]+)\]?", r"[\1:\2]", string)
        
        string = re.sub(r" SMALL ", r" ", string)
        string = re.sub(r" LARGE ", r" ", string)
        
        if instr != None:
            part1 = string + ' '*(40-len(string))
            self.nasmfw.write(part1)
            
            part2 = "; original@[%08x]:[%s]" % (instr.GetOriginEA(), instr.GetDisasm())
            self.nasmfw.write(part2)
            
            part3 = ' '*(100-len(part1)-len(part2)) + "bytecode:[\\x%s]" % '\\x'.join(['%02x' % ord(x) for x in instr.GetOpcode()])
            self.nasmfw.write(part3)
            
            comment = instr.GetComment()
            if comment != None:
                self.nasmfw.write('###%s###' % comment)
            self.nasmfw.write("\n")
            
        else:
            self.nasmfw.write(string)
        
    def NasmAssemble(self, function_ea, write_ea):
        dir = self.opty_dir
        
        nasm = "C:\\Program Files\\nasm\\nasm.exe"
        arg1 = "f_%08x.asm" % function_ea
        arg2 = "-o f_%08x.o" % function_ea
        arg3 = "-l f_%08x.lst" % function_ea
        arg4 = "-Ox"
        
        orig_dir = os.getcwd()
        os.chdir(dir)
        
        idc.Batch(0)
        while 1:
            try:
                p = subprocess.Popen([nasm, arg1, arg2, arg3, arg4], stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.PIPE)
                o, e = p.communicate()
                
                if o != "": print o
                if e != "": print e
                
                fop = open("f_%08x.o" % function_ea, "rb")
                
                ans = idaapi.askyn_c(0, "HIDECANCEL\nDo you want to manually edit function before writing to IDA?")
                if ans == 1:
                    os.startfile(arg1, "open")
                    idaapi.warning("Press OK button when you're done editing file.")
                    fop.close()
                    continue
                else:
                    idc.Batch(1)
                    break
            
            except:
                error_msg = '\n'.join(e.split("\n")[:15])
                
                os.startfile(arg1, "open")
                ans = idaapi.askyn_c(1, """HIDECANCEL\nNASM failed to assemble [f_%08x.o] file.
You can manually edit and NASM this file [f_%08x.asm] and click Yes when you're done.
File is located in directory where your IDB is located.
If you want to skip this function press No.

Nasm output:
%s""" % (function_ea, function_ea, error_msg))
                
                if ans == 1:
                    continue
                else:
                    os.chdir(orig_dir)
                    idc.Batch(1)
                    return None
        
        os.chdir(orig_dir)
        
        print ">>>Writing function [%08x] @ [%08x]" % (function_ea, write_ea)
        
        data = fop.read()
        data_len = len(data)
        for offset in xrange(0, data_len):
            idc.PatchByte(write_ea+offset, ord(data[offset]))
        fop.close()
        
        idc.MakeCode(write_ea)
        
        fp = open("%s\\f_%08x.lst" % (dir, function_ea), "r")
        asm_lst = fp.read()
        
        base_addr = re.search(r"ORG ([\dABCDEF]+)H", asm_lst).group(1)
        base_addr = int(base_addr, 16)
        
        for jt in self.jmp_table_refs:
            m = re.search(r"\s*\d+\s+([\dABCDEF]{8}).*?%s" % re.escape(jt), asm_lst, re.IGNORECASE)
            if m != None:
                jt_ea = int(m.group(1), 16)
                jt_str = re.search(r"SJ_.{8}", jt, re.IGNORECASE).group()
                for m in re.findall(r"(?i)\n\s*\d+\s+[\dABCDEF]{8}\s+.*?\s+%s" % re.escape(jt_str), asm_lst):
                    r = re.search(r"\d+\s([\dABCDEF]{8})", m.strip(), re.IGNORECASE).group(1)
                    
                    #print "AddCodeXref(0x%08x, 0x%08x, idc.XREF_USER)" % (jt_ea+base_addr, idc.Dword(int(r, 16)+base_addr))
                    idc.AddCodeXref(jt_ea+base_addr, idc.Dword(int(r, 16)+base_addr), idc.XREF_USER)
            else:
                raise MiscError
        
        for line in asm_lst.split("\n"):
            comment = re.search(r"###(.*?)###", line)
            if comment != None:
                data = re.search(r"\s*\d+\s([\dABCDEF]+)\s([\dABCDEF\(\)]+)", line)
                if data != None:
                    offset = int(data.group(1), 16)
                    idc.MakeComm(write_ea+offset, comment.group(1))
                
        fp.close()
        
        return write_ea + data_len + 10

    def AllocateCodeSegment(self):
        if self.segment_start != 0:
            self.FreeCodeSegment()
        
        while True:
            seg_start = idaapi.BADADDR
            while seg_start == idaapi.BADADDR:
                seg_start = idc.AskAddr(0x1000, "Enter address to create new code segment")
            
            seg_size = 0
            while seg_size == 0:
                seg_size = idc.AskAddr(0x10000, "Enter size of new code segment")
            
            if idc.SegCreate(seg_start, seg_start+seg_size, 0, 1, 0, 0) != 0:
                break
        
        self.segment_start = seg_start
        self.segment_size = seg_size
        
        while True:
            seg_name = ''
            while seg_name == '':
                seg_name = idc.AskStr("optimized", "Enter a new segment name")
                
            if idc.SegRename(self.segment_start, seg_name) != 0:
                break
        self.segment_name = seg_name
        
        self.free_ea = self.segment_start

    def FreeCodeSegment(self):
        while True:
            if idc.SegDelete(self.segment_start, 0) == 0:
                break

    def BuildAsmString(self, instr, function):
        if instr.GetMnem() == 'retn':
            mnem = 'ret '
        else:
            if instr.GetMnemPrefix(1) != '':
                mnem = instr.GetMnemPrefix(1) + ' ' + instr.GetMnem(1) + ' '
            else:
                mnem = instr.GetMnem(1) + ' '
        
        refs = list(function.GetRefsFrom(instr.GetOriginEA()))
        if len(refs) > 1 and instr.GetMnem() != "jmp":
            key = refs[0][0] if refs[0][1] else refs[1][0]
            
            if self.nasm:
                self.NasmWriteToFile("\t%s L%08x" % (instr.GetMnem(1), key), instr)
            else:
                if self.bb_head_ea.has_key(key):
                    mnem += '%09xh' % self.bb_head_ea[key]
                    return mnem
                
                else:
                    for i in xrange(0,6):
                        idc.PatchByte(self.free_ea + i, 0x90)
                    
                    if self.jmp_deps.has_key(key):
                        self.jmp_deps[key].append(self.free_ea)
                    else:
                        self.jmp_deps[key] = [self.free_ea]
                    
                    self.ref_instr[self.free_ea] = instr
                    self.free_ea += 6
                    
            return ''
        
        if instr.GetMnem() == 'call':
            if instr.GetOpndType(1) in [2,5,6]:
                mnem += '%09xh' % instr.GetOpndValue(1)
            elif instr.GetOpndType(1) == 7:
                comment = instr.GetComment()
                if comment != None and comment == "Artificial: Gen from call $+5":
                    mnem += '$+5'
                else:
                    mnem += '%09xh' % instr.GetOpndValue(1)
                
            elif instr.GetOpndType(1) == 1:
                mnem += instr.GetOpnd(1)
            else:
                mnem += instr.GetOpnd(1)
                
            if self.nasm:
                self.NasmWriteToFile("\t%s" % mnem, instr)
            
            return mnem
        
        elif instr.GetMnem() == 'jmp':
            if self.nasm:
                tref_from = list(function.GetRefsFrom(instr.GetOriginEA()))[0][0]
                
                if tref_from == None:
                    #can be unknown
                    if debug:
                        print ">Assemble:BuildAsmString - tref_from = None @ [%08x] " % instr.GetOriginEA(), instr.GetOpnd(1)
                    
                    if instr.GetOpndType(1) == 2:
                        size_prefix = idaapi.get_item_size(instr.GetOpndValue(1))
                        self.NasmWriteToFile("\tjmp %s 0x%08x" % (instr.BytesToPrefix(size_prefix), instr.GetOpndValue(1)), instr)
                    else:
                        self.NasmWriteToFile("\tjmp %s" % instr.GetOpnd(1), instr)
                else:
                    if len(refs) > 1:
                        instr_string = "jmp %s" % instr.GetOpnd(1).replace("SUBS", "sj_%08x_1" % instr.GetOriginEA())
                        self.NasmWriteToFile("\t%s\n" % instr_string )
                        
                        self.jmp_table_refs.append(instr_string)
                        
                        self.jmp_table += "\n"
                        #self.NasmWriteToFile("\tsj_%08x " % instr.GetOriginEA())
                        
                        counter = 1
                        name = 'sj_%08x' % instr.GetOriginEA()
                        for ref in refs:
                            #self.NasmWriteToFile("%s_%d dd L%08x\n" % (name, counter, ref[0]))
                            self.jmp_table += "%s_%d dd L%08x\n" % (name, counter, ref[0])
                            counter += 1
                    else:
                        self.NasmWriteToFile("\tjmp L%08x" % tref_from, instr)
                    
                return None
            
            if debug:
                print ">Assemble:BuildAsmString - Got mnem JMP ", refs
            
            if len(refs) > 1:
                key = refs[0][0] if refs[0][1] else refs[1][0]
            else:
                key = refs[0][0]
                
            if self.bb_head_ea.has_key(key):
                mnem += '%xh' % self.bb_head_ea[key]
                return mnem
            
            elif refs[0][0] == None:
                #NOTICE!
                mnem += instr.GetOpnd(1)
                return mnem
            
            else:
                for i in xrange(0,6):
                    idc.PatchByte(self.free_ea + i, 0x90)
                
                if self.jmp_deps.has_key(key):
                    self.jmp_deps[key].append(self.free_ea)
                else:
                    self.jmp_deps[key] = [self.free_ea]
                
                self.ref_instr[self.free_ea] = instr
                self.free_ea += 6
                return None
        
        #regular (non CFG) instruction
        if instr.GetOpnd(1) != None and instr.GetOpnd(1) != '':
            if instr.GetOpndType(1) == 2 and re.search(r"\*.*?\+", instr.GetOpnd(1)) == None:
                op_size = idaapi.get_item_size(instr.GetOpndValue(1))
                
                op_pref_size = instr.GetOpndPrefixSize(1)
                if op_pref_size != None:
                    op_size = op_pref_size
                
                op_size_2 = 0
                if instr.GetOpndType(2) == 1:
                    op_size_2 = instr.GetRegSize(instr.GetOpnd(2))
                    
                if op_size >= op_size_2:
                    opnd = '%s [0x%08x]' % (instr.BytesToPrefix(op_size), instr.GetOpndValue(1))
                else:
                    opnd = '%s [0x%08x]' % (instr.BytesToPrefix(op_size_2), instr.GetOpndValue(1))
                    
                mnem += opnd
            
            elif instr.GetOpndPrefix(1) != None:
                mnem += '%s %s' % (instr.GetOpndPrefix(1), instr.GetOpnd(1))
            
            else:
                mnem += instr.GetOpnd(1)
            
            if instr.GetOpnd(2) != None:
                if instr.GetOpndType(2) == 2 and re.search(r"\*+", instr.GetOpnd(2)) == None:
                    op_disas = instr.GetOpnd(2)
                    op_size = idaapi.get_item_size(instr.GetOpndValue(2))
                    
                    op_pref_size = instr.GetOpndPrefixSize(1)
                    if op_pref_size != None:
                        op_size = op_pref_size
                        
                    
                    op_size_2 = 0
                    if instr.GetOpndType(1) == 1:
                        op_size_2 = instr.GetRegSize(instr.GetOpnd(1))
                        
                    if op_size >= op_size_2:
                        opnd = '%s [0x%08x]' % (instr.BytesToPrefix(op_size), instr.GetOpndValue(2))
                    else:
                        opnd = '%s [0x%08x]' % (instr.BytesToPrefix(op_size_2), instr.GetOpndValue(2))

                    if instr.GetMnem() == "lea":
                        opnd = '[0x%08x]' % (instr.GetOpndValue(2))
                        mnem += ', ' + opnd
                    else:
                        mnem += ', ' + opnd
                    
                else:
                    mnem += ', ' + instr.GetOpnd(2)
                
        elif instr.GetOpnd(2) != None and instr.GetOpnd(2) != '':
            if instr.GetOpndType(2) == 2 and re.search(r"\*+", instr.GetOpnd(2)) == None:
                op_disas = instr.GetOpnd(2)
                op_size = idaapi.get_item_size(instr.GetOpndValue(2))
                
                op_pref_size = instr.GetOpndPrefixSize(2)
                if op_pref_size != None:
                    op_size = op_pref_size
                
                op_size_2 = 0
                if instr.GetOpndType(1) == 1:
                    op_size_2 = instr.GetRegSize(instr.GetOpnd(1))
                    
                if op_size >= op_size_2:
                    opnd = '%s [0x%08x]' % (instr.BytesToPrefix(op_size), instr.GetOpndValue(2))
                else:
                    opnd = '%s [0x%08x]' % (instr.BytesToPrefix(op_size_2), instr.GetOpndValue(2))
                
                mnem += opnd
            
            elif instr.GetOpndType(2) == 3 and instr.GetMnem().upper()[:2] == "FS":
                #this is a special case to handle FS* fp instructions that have 1st argument hidden in IDA
                #and to handle the difference in masm vs nasm (tbyte bs tword).
                
                #NOTE: GetOpnd(1,1) is used because the first argument is empty when it gets populated
                # by the taint function, so original operand is in GetOpnd(2,0) and cleand (no prefix)
                # operand is in GetOpnd(1,1)
                opnd = '%s %s' % (instr.BytesToPrefix(instr.GetOpndPrefixSize(1)), instr.StripOpndPrefix(instr.GetOpnd(2)))
                mnem += ' ' + opnd
                
            else:
                mnem += ' ' + instr.GetOpnd(2)
            
        
        if self.nasm:
            self.NasmWriteToFile("\t%s" % mnem, instr)
        
        return mnem

    def AsmAndWrite(self, mnem, instr=None, write_ea=None, function=None):
        if mnem == '':
            return
        
        if write_ea != None:
            ea_write = write_ea
        else:
            ea_write = self.free_ea
        
        idc.MakeUnkn(ea_write, 0)
        #tmp = idaapi.assemble(self.free_ea, self.segment_start, self.free_ea, 1, mnem)

        if debug:
            print ">Assemble:AsmAndWrite - !Writing @ ea[%08x] ip[%08x] instr[%s]" % (ea_write, ea_write, mnem)
        tmp = idaapi.assemble(ea_write, 0, ea_write, 1, mnem)
        
        if instr != None:
            idaapi.set_cmt(ea_write, "%08x" % instr.GetOriginEA(), 0)
        
        if tmp == 0:
            if instr == None and function != None:
                raise MiscError
            
            if debug:
                print '>Assemble:AsmAndWrite - !Messy instruction', mnem
                print '>Assemble:AsmAndWrite - Trying original opcodes!'
            
            refs_from = [x for x in function.GetRefsFrom(instr.GetOriginEA()) if x != None]
            if len(refs_from) == 0:
                if instr.GetIsModified() == True:
                    raise MiscError
                
                instr_op = instr.GetOpcode()
                for pos in xrange(0, len(instr_op)):
                    idc.PatchByte(ea_write+pos, ord(instr_op[pos]))
                
                if idc.MakeCode(ea_write) == 0:
                    raise MiscError
                
                ea_write += idc.ItemSize(ea_write)
            
            elif len(refs_from) == 1:
                instr_op = instr.GetOpcode()
                for pos in xrange(0, len(instr_op)):
                    idc.PatchByte(ea_write+pos, ord(instr_op[pos]))
                
                if idc.MakeCode(ea_write) == 0:
                    raise MiscError
                
                ea_write += idc.ItemSize(ea_write)
                
            else:
                #print '>Assemble:AsmAndWrite - GetRefsFrom(%08x)' % instr.GetOriginEA(), [hex(x) for x in function.GetRefsFrom(instr.GetOriginEA()) if x != None]
                print '>Assemble:AsmAndWrite - refs_from', refs_from
                print '>Assemble:AsmAndWrite - ea_write [%08x]' % ea_write
                print '>Assemble:AsmAndWrite - mnem', mnem
                print '>Assemble:AsmAndWrite - instr.GetMnem', instr.GetMnem()
                print '>Assemble:AsmAndWrite - instr.GetDisasm', instr.GetDisasm()
                raise MiscError
        else:
            if idc.MakeCode(ea_write) == 0:
                raise MiscError
            
            ea_write += idc.ItemSize(ea_write)
            
        if write_ea == None:
            self.free_ea = ea_write
            

    def AsmAndWriteBranches(self, function):
        for ea in self.jmp_deps.iterkeys():
            if ea == None:
                continue
            if self.bb_head_ea.has_key(ea):
                for branch_ea in self.jmp_deps[ea]:
                    if debug:
                        print '>Assemble:AsmAndWriteBranches - ea[%08x] <- branch_ea[%08x]' % (ea, branch_ea)
                        print '>Assemble:AsmAndWriteBranches - ref_instr', self.ref_instr[branch_ea]
                    
                    mnem = self.BuildAsmString(self.ref_instr[branch_ea], function)
                    self.AsmAndWrite(mnem, self.ref_instr[branch_ea], branch_ea, function)
                
            else:
                print ">Assemble:AsmAndWriteBranches - !Branch @ %08x no BB head reference" % ea
                raise MiscError
        
        return None

    def Assemble(self, function, nasm=True):
        '''
            Main Assemble Function
        '''
        
        if self.functions.has_key(function.start_ea):
            ans = idaapi.askyn_c(1, "HIDECANCEL\nFunction @ [%08x] was already optimized, are you sure you want to overwrite old one?")
            if ans == 0:
                return
        
        idc.Batch(1)
        
        self.jmp_table = ""
        self.jmp_table_refs = []
        self.jmp_deps = {}
        self.ref_instr = {}
        self.bb_head_ea = {}
        
        function_ea = self.free_ea
        function_end = None
        
        if debug:
            print ">Assemble(%08x) - Starting" % function.start_ea
        
        if nasm:
            if self.opty_dir == None:
                self.opty_dir = idc.GetIdbPath()
                self.opty_dir = self.opty_dir[:self.opty_dir.rfind(os.sep)] + os.sep + "optimice_%s" % idc.GetInputFile()
                if not os.path.isdir(self.opty_dir):
                    os.mkdir(self.opty_dir)
            
            self.nasm = True
            self.nasmfw = open(self.opty_dir + os.sep + 'f_%08x.asm' % function.start_ea, "w+")
            self.NasmWriteToFile("[BITS 32]\n")
            self.NasmWriteToFile("\torg %09xh\n" % function_ea)
        else:
            self.nasm = False
        
        for bb_ea in function.DFSFalseTraverseBlocks():
            if self.nasm:
                self.NasmWriteToFile("\nL%08x:\n" % bb_ea)
                self.bb_head_ea[bb_ea] = True
            else:
                self.bb_head_ea[bb_ea] = self.free_ea
            
            for instr in function.GetBBInstructions(bb_ea):
                if instr == None:
                    continue
                    
                mnem = self.BuildAsmString(instr, function)
                
                if debug:
                    print ">Assemble - Assembling @ %08x [%s]" % (instr.GetOriginEA(), mnem)
                
                if not self.nasm:
                    self.AsmAndWrite(mnem, instr, function=function)
            
            if not instr.IsCFI():
                ref_from = list(function.GetRefsFrom(instr.GetOriginEA()))[0][0]
                
                if self.bb_head_ea.has_key(ref_from):
                    if self.nasm:
                        self.NasmWriteToFile("\tjmp L%08x ; \n" % ref_from)
                    else:
                        self.AsmAndWrite("jmp %09xh" % self.bb_head_ea[ref_from])
            
            elif instr.GetMnem() == "call":
                for ref,path in function.GetRefsFrom(instr.GetOriginEA()):
                    if path == False:
                        if self.bb_head_ea.has_key(ref):
                            if self.nasm:
                                self.NasmWriteToFile("\tjmp L%08x ; ###FAKE 2 JMP###\n" % ref)
                            else:
                                self.AsmAndWrite("jmp %09xh" % self.bb_head_ea[ref])
            
            elif instr.IsJcc():
                ref_from = list(function.GetRefsFrom(instr.GetOriginEA()))
                for ref,path in ref_from:
                    if path == False:
                        break
                
                if path == True:
                    raise MiscError
                
                elif self.bb_head_ea.has_key(ref):
                    print "Check this out @ [%08x] ref:[%08x]" % (instr.GetOriginEA(), ref)
                    if self.nasm:
                        self.NasmWriteToFile("\tjmp L%08x ; ###FAKE 2 JMP###\n" % ref)
                    else:
                        self.AsmAndWrite("jmp %09xh" % self.bb_head_ea[ref])
        
        ret = None
        if self.nasm:
            self.NasmWriteToFile(self.jmp_table)
            
            self.nasmfw.close()
            self.nasmfw = None
            
            ret = self.NasmAssemble(function.start_ea, self.free_ea)
            if ret != None:
                self.free_ea = ret
        else:
            ret = self.AsmAndWriteBranches(function)
            self.free_ea = ret
        
        self.ref_instr = {}
        idc.Batch(0)
        
        if ret != None:
            idc.MakeFunction(function_ea)
            
            comment = idc.Comment(function_ea)
            if comment != None:
                comment = 'Origin@[%08x]; %s' % (function.start_ea, comment)
            else:
                comment = 'Origin@[%08x];' % function.start_ea
                
            idc.MakeComm(function_ea, comment)
            
            comment = idc.Comment(function.start_ea)
            if comment != None:
                comment = 'OPTY@[%08x]; %s' % (function_ea, comment)
            else:
                comment = 'OPTY@[%08x];' % function_ea
                
            idc.MakeComm(function.start_ea, comment)
            
            idaapi.set_name(function_ea, "om_%s" % idc.Name(function.start_ea))
            
        function_end = self.free_ea
        self.functions[function.start_ea] = (function_ea, function_end)
        
        idaapi.refresh_idaview_anyway()
