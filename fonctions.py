# fonctions.py

from syntax import *

#=======================================================================    
# fonction evaluation
#=======================================================================

def eval(f: Formula) -> bool:
    if isinstance(f, ConstF ):
        return f.val
    
    elif isinstance(f, ComparF ):
        if f.op == Eq():
            return (f.left == f.right)
        else :
            return (f.left != f.right)
        
    elif isinstance(f,NotF):
        return not eval(f.sub)
    
    elif isinstance(f,BoolOpF) :
        if isinstance(f.op,Conj):
            return (eval(f.left) and eval(f.right))
        else :
            return (eval(f.left) or eval(f.right))
    
    else :
        raise ValueError("Formule Quantifiée")

#=======================================================================    
# fonction dualOp et dual
#=======================================================================

def dualOp (op: BoolOp ) -> BoolOp :
    if isinstance (op , Conj ):
        return (Disj ())
    else:
        return (Conj ())
    
def dual(f: Formula ) -> Formula :
    if isinstance (f, ConstF ):
        return f
    elif isinstance (f, ComparF ):
        return f
    elif isinstance (f, NotF ):
        return NotF(dual(f.sub ))
    elif isinstance (f, BoolOpF ):
        return BoolOpF (dual(f.left), dualOp (f.op), dual(f. right ))
    else:
        raise ValueError ("dual applied to quantified formula ")

#=======================================================================    
# fonction pretraitement
#=======================================================================

def pretraitement(f: Formula) -> Formula :
    """
    (a) ¬(z ≺ z 0 ) ↔ (z = z 0 ∨ z 0 ≺ z)
    (b) ¬(z = z 0 ) ↔ (z ≺ z 0 ∨ z 0 ≺ z)    
    """
    if isinstance (f, ConstF ):
        return f
    
    elif isinstance (f, ComparF ):
        return f
    
    elif isinstance (f, BoolOpF ):
        return BoolOpF (pretraitement(f.left), f.op, pretraitement(f. right ))
    
    elif isinstance (f, NotF ):
        
        if isinstance (f.sub, ComparF ):
            if isinstance(f.sub.op, Lt ) :             #cas (a) ¬(z ≺ z 0 ) ↔ (z = z 0 ∨ z 0 ≺ z)
                return ComparF (ComparF (f.sub.left,Eq(),f  .sub.right),
                                Disj(),
                                ComparF (f.sub.right,Lt(),f.sub.left))
            
            elif isinstance(f.sub.op, Eq ) :           #cas (b) ¬(z = z 0 ) ↔ (z ≺ z 0 ∨ z 0 ≺ z)  
                return ComparF (ComparF (f.sub.left,Lt(),f.sub.right),
                                Disj(),
                                ComparF (f.sub.right,Lt(),f.sub.left))
            
            else :
                return NotF(pretraitement(f.sub))
            
        else :
                return NotF(pretraitement(f.sub))
        
    else:
        raise ValueError ("pretraitement applied to quantified formula ")