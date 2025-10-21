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

def pretraitement(f: Formula) -> Formula:
    """
    Prétraitement d'une formule de la forme ∃x. φ :
    1. Tirer les négations à l'intérieur (forme normale négative)
        (1) ¬ a ^ b ↔ ¬a ∨ ¬b
        (2) ¬ a ∨ b ↔ ¬a ^ ¬b
    2. Éliminer les négations devant les relations :
       (a) ¬(z ≺ z') ↔ (z = z' ∨ z' ≺ z)
       (b) ¬(z = z') ↔ (z ≺ z' ∨ z' ≺ z)
    3. Transformer en forme normale disjonctive
    4. Tirer les quantificateurs à l’intérieur des disjonctions
    """
    
    if isinstance(f, ConstF) or isinstance(f, ComparF) : # Cas d'arrêt
        return f
    
    elif isinstance(f, BoolOpF) : # Cas des opérateur
        return BoolOpF(pretraitement(f.left),f.op,pretraitement(f.right))
    
    elif isinstance(f,NotF) : # Cas du not
        sub = f.sub

        if isinstance(sub, NotF) :
            return pretraitement(sub.sub)
        
        elif isinstance(sub, BoolOpF) :
            if isinstance(sub.op, Conj) :
                return BoolOpF(pretraitement(NotF(sub.left)), Disj(), pretraitement(NotF(sub.right)))
            
            elif isinstance(sub.op, Disj) :
                return BoolOpF(pretraitement(NotF(sub.left)), Conj(), pretraitement(NotF(sub.right)))

        elif isinstance(sub, ComparF) :
            if isinstance(sub.op, Lt) :
                return BoolOpF(
                    ComparF(sub.left, Eq(), sub.right),
                    Disj(),
                    ComparF(sub.right, Lt(), sub.left)
                )
            elif isinstance(sub.op, Eq) :
                return BoolOpF(
                    ComparF(sub.left, Lt(), sub.right),
                    Disj(),
                    ComparF(sub.right, Lt(), sub.left)
                )
        else :
            return f
    
    elif isinstance(f,QuantifF) : # On se place aprés les quantificateurs
        return QuantifF(f.q,f.var,pretraitement(f.body))
    
    else :
        return ValueError("Formule inconnue pour le prétraitement.")