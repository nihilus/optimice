import idc
import idaapi

import Function
import Assembler
import CFGOptimization
import BlockTainting
import CodeOptimization

import GUI_FunctionManager

import pickle
import traceback

def optimice():
    ea = idc.ScreenEA()
    print "Starting optimization @ [%08x]" % ea
    
    f = Function.Function(ea)    
    cfg = CFGOptimization.ReduceJMP(f)
    peep = CodeOptimization.PeepHole(f)
    dead = CodeOptimization.DeadCodeElimination(f)
    
    modified = True
    while modified:
        modified = False
        
        f.AssertCFGStructure()
        modified |= cfg.Reduce()
        
        modified |= cfg.JccReduce()
        
        modified |= cfg.JccReduceComplementary()
        
        modified |= peep.OptimizeFunction()
        
        modified |= dead.OptimizeFunction()
        
        f.CleanUp()
        
        #f.PrintBlocks()
    
    f.CleanUp()
    f.AssertCFGStructure()
    
    #f.PrintBlocks()
    
    asms = Assembler.LoadSavedAssemblers()
    
    if asms != None and len(asms.keys()) > 1:
        print "Ask user to choose one!"
    elif asms != None and len(asms.keys()) == 1:
        asm = asms.values()[0]
    else:
        asm = Assembler.Assemble()
    
    asm.Assemble(f)
    asm.SaveState()
    
    print "Optimization ended!"
    
def wrapper():
    try:
        optimice()
    except:
        print "-------------"
        traceback.print_exc()
        print "-------------"
        idc.Warning("---Please send the error message from the output window to: gljiva@gmail.com---")

def setHotkey():    
    err = idaapi.CompileLine(r"""
    static key_ALTN()
    {
      RunPythonStatement("wrapper()");
    }
    """)
    
    if err:
        print "Error compiling IDC code: %s" % err
        return 
    else:
        # Add the hotkey
        AddHotkey("ALT-N", 'key_ALTN')
    
    print "Optimice v0.14 initialized"
    print "To optimize use ALT+N hotkey and position cursor at the beginning of code!"
    
    #Remove it with
    #DelHotkey('key_ALTN')

def Nop():
    pass

if __name__ == "__main__":
    idaapi.add_menu_item("Edit/Plugins/", "-", "", 0, Nop, ())
    idaapi.add_menu_item("Edit/Plugins/", "Optimice: Manage functions", "", 0, GUI_FunctionManager.Caller, ())
    idaapi.add_menu_item("Edit/Plugins/", "Optimice: Optimize (ALT+N)", "", 0, optimice, ())
    idaapi.add_menu_item("Edit/Plugins/", "-", "", 0, Nop, ())
    
    #optimice()
    setHotkey()
    

