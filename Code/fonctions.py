# ...existing code...
from syntax import *

#=======================================================================    
# fonction str_list
#=======================================================================
# @brief cette fonction retourne une représentation en chaîne de caractères
#   d'une formule logique.
#   @param formula : Formula
#   @param implication_mode : bool
#   @return str
def display_formula (formula: Formula, implication_mode: bool = True):
    
    if isinstance(formula, ConstF):
        return "⊤" if formula.val else "⊥"
    
    if isinstance(formula, ComparF):
        return f"({formula.left} {formula.op} {formula.right})"
    
    if isinstance(formula, NotF):
        return "¬" + display_formula(formula.sub, implication_mode)
    
    if isinstance(formula, BoolOpF):
        op = formula.op
        elems = formula.elements
        # detect implication pattern (or (not A) B)
        if implication_mode and isinstance(op, Disj) and len(elems) == 2 and isinstance(elems[0], NotF):
            return f"({display_formula(elems[0].sub, implication_mode)} → {display_formula(elems[1], implication_mode)})"
        sep = " ∧ " if isinstance(op, Conj) else " ∨ "
        return "( " + sep.join(display_formula(e, implication_mode) for e in elems) + " )"
    
    if isinstance(formula, QuantifF):
        q = "∀" if isinstance(formula.q, All) else "∃"
        return f"{q}{formula.var}.{display_formula(formula.body, implication_mode)}"

    raise ValueError("type of formula is not recognized")

#=======================================================================    
# fonction dualOp et dual
#=======================================================================
# @brief cette fonction retourne la formule obtenue en remplaçant
#   toutes les conjonctions par des disjonctions et réciproquement,
#
#   @param formula : Formula
#   @return Formula
#   @raise ValueError type of formula is not allowed
def dualOp (formula: Formula):
    
    if isinstance(formula, BoolOpF):
        new_op = Disj() if isinstance(formula.op, Conj) else Conj()
        return BoolOpF(new_op, formula.elements)
    
    raise ValueError("type of formula is not allowed")

# @brief cette fonction retourne la formule duale de la formule donnée
#   en remplaçant toutes les conjonctions par des disjonctions et réciproquement,
#   et en remplaçant chaque sous-formule par sa duale.
#   @param formula : Formula
#   @return Formula
#   @raise ValueError Formula with quantifiers is not allowed 
def dual(formula : Formula | tuple ):

    if isinstance(formula, (ConstF, ComparF)):
        return formula
    
    elif isinstance(formula, NotF):
        return NotF(dual(formula.sub))
    
    elif isinstance(formula, BoolOpF):
        new_op = Disj() if isinstance(formula.op, Conj) else Conj()
        return BoolOpF(new_op, [dual(e) for e in formula.elements])
    
    else :
        raise ValueError("Formule with quantifiers not allowed")

#=======================================================================    
# fonction eval
#=======================================================================
# @brief cette fonction evalu une une formule sans quantificateurs (attention aux comparaisons)
#   @param f : Formula
#   @return bool
#   @raise ValueError Formula with quantifiers is not allowed
def eval(formula: Formula) -> bool:
    
    if isinstance(formula, ConstF ):
        return formula.val
    
    elif isinstance(formula, ComparF ):
        
        if isinstance(formula.op, Eq):
            return (formula.left == formula.right)
        else:
            return (formula.left < formula.right)
        
    elif isinstance(formula, NotF):
        return (not eval(formula.sub))
    
    elif isinstance(formula, BoolOpF) :
        
        if isinstance(formula.op, Conj): #conseil de la partie B2
            return all(eval(e) for e in formula.elements)
        
        else:
            return any(eval(e) for e in formula.elements)
    
    else :
        raise ValueError("Formula with quantifiers is not allowed")