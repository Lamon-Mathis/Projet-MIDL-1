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


#=======================================================================
# fonction nnf
#=======================================================================
# @brief transforme une formule en forme normale négative (NNF)
# c’est-à-dire que les négations ne portent que sur des formules atomiques.
#=======================================================================
def nnf(formula: Formula) -> Formula:
    if isinstance(formula, (ConstF, ComparF)):
        return formula

    elif isinstance(formula, NotF):
        sub = formula.sub
        if isinstance(sub, ConstF):
            return ConstF(not sub.val)
        elif isinstance(sub, ComparF):
            return formula 
        elif isinstance(sub, NotF):
            return nnf(sub.sub)
        elif isinstance(sub, BoolOpF):
            new_op = Conj() if isinstance(sub.op, Disj) else Disj()
            new_elements = [nnf(NotF(e)) for e in sub.elements]
            return BoolOpF(new_op, new_elements)
        else:
            raise ValueError("Formule avec quantificateurs non supportée pour nnf")

    elif isinstance(formula, BoolOpF):
        return BoolOpF(formula.op, [nnf(e) for e in formula.elements])

    else:
        raise ValueError("Formule avec quantificateurs non supportée pour nnf")

#=======================================================================
# fonction dnf
#=======================================================================
# @brief transforme une formule en forme normale disjonctive (DNF)
# c’est-à-dire une disjonction de conjonctions de littéraux.
#=======================================================================
def dnf(formula: Formula) -> Formula:
    # on commence par mettre en forme normale négative
    formula = nnf(formula)

    # fonction auxiliaire : distribue ∧ sur ∨
    def distrib(f1: Formula, f2: Formula) -> Formula:
        if isinstance(f1, BoolOpF) and isinstance(f1.op, Disj):
            return BoolOpF(Disj(), [distrib(e, f2) for e in f1.elements])
        elif isinstance(f2, BoolOpF) and isinstance(f2.op, Disj):
            return BoolOpF(Disj(), [distrib(f1, e) for e in f2.elements])
        else:
            return BoolOpF(Conj(), [f1, f2])

    if isinstance(formula, (ConstF, ComparF, NotF)):
        return formula

    elif isinstance(formula, BoolOpF):
        elems = [dnf(e) for e in formula.elements]
        if isinstance(formula.op, Disj):
            # a ∨ b ∨ c ...
            flat = []
            for e in elems:
                if isinstance(e, BoolOpF) and isinstance(e.op, Disj):
                    flat.extend(e.elements)
                else:
                    flat.append(e)
            return BoolOpF(Disj(), flat)
        elif isinstance(formula.op, Conj):
            # distribuer sur les disjonctions
            result = elems[0]
            for e in elems[1:]:
                result = distrib(result, e)
            return result
    else:
        raise ValueError("Formule avec quantificateurs non supportée pour dnf")


