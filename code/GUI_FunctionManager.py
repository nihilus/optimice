import os
import shutil
import re

import idaapi
import idc
import Assembler
from idaapi import Choose2

class ChooseFunctions(Choose2):
    def __init__(self, title):
        Choose2.__init__(self, title, [ ["Segment", 9], ["Function name", 20], ["Address", 9], ["Opty name", 20], ["Address", 9] ])
        self.n = 0
        self.items = self.populate_items()
        self.popup_names = ["", "Delete", "Delete Segment", "Refresh"]
    
    def OnEditLine(self, n):
        #this is "Delete Segment"
        ans = idaapi.askyn_c(1, "HIDECANCEL\nAre you sure you want to delete segment and all optimized data from disk?")
        
        if ans == 1:
            opty_dir = idc.GetIdbPath()
            opty_dir = opty_dir[:opty_dir.rfind(os.sep)] + os.sep + "optimice_%s" % idc.GetInputFile()
            
            print opty_dir
            if not os.path.isdir(opty_dir):
                print ">GUI_FunctionManager:OnEditLine - Error [%s] not a directory!" % opty_dir
                return 0
        
            shutil.rmtree(opty_dir)
            print ">GUI_FunctionManager: Optimice directory deleted: [%s]" % opty_dir
            
            idc.SegDelete(int(self.items[n][0], 16), 0)
            print ">GUI_FunctionManager: Optimice segment deleted: [%s]" % self.items[n][0]
        
        self.populate_items()
        return 0

    def OnGetSize(self):
        return len(self.items)

    def OnClose(self):
        pass

    def OnCommand(self, n, cmd_id):
        return 1

    def OnGetLineAttr(self, n):
        return

    def OnDeleteLine(self, n):
        ans = idaapi.askyn_c(1, "HIDECANCEL\nAre you sure you want to delete function [%s] @ [%s]?" % (self.items[n][3], self.items[n][4]) )
        if ans == 1:
            asms = Assembler.LoadSavedAssemblers()
            item = int(self.items[n][2], 16)
            if asms != None and len(asms.keys()) > 0:
                for asm in asms.itervalues():
                    if asm.functions.has_key(item):
                        print "Removed [%08x]!" % item
                        del asm.functions[item]
                        asm.SaveState()
            
            opty_ea = int(self.items[n][4], 16)
            print "set_name[%08x]" % opty_ea
            idc.MakeComm(opty_ea, "")
            idaapi.set_name(opty_ea, "")
            idc.DelFunction(opty_ea)
            
            comment = idc.Comment(item)
            comment = re.sub(r"(?i)OPTY@\[[\d+abcdef]+\];\s*", "", comment)
            idc.MakeComm(item, comment)
            
        self.populate_items()
        return n

    def OnRefresh(self, n):
        self.populate_items()
        n = self.OnGetSize()
        return n

    def OnSelectLine(self, n):
        tform = idaapi.open_disasm_window("%s" % self.items[n][3])
        idaapi.switchto_tform(tform, 1)
        idc.Jump(int(self.items[n][4], 16))

    def OnGetLine(self, n):
        #print("getline %d" % n)
        return self.items[n]

    def show(self):
        t = self.Show()
        if t < 0:
            print "Error"
            return False
        return True

    def populate_items(self):
        asms = Assembler.LoadSavedAssemblers()
        lst = []
        
        if asms != None and len(asms.keys()) > 0:
            for asm in asms.itervalues():
                for key in asm.functions.iterkeys():
                    lst.append(["%08x" % asm.segment_start, idc.GetFunctionName(key), "%08x" % key, idc.GetFunctionName(asm.functions[key][0]), "%08x" % asm.functions[key][0]])
                
        del asms
        self.items = lst
        
        return self.items

def Caller():
    c = ChooseFunctions("Optimice")
    r = c.show()

if __name__ == "__main__":
    c = ChooseFunctions("Optimice")
    r = c.show()


