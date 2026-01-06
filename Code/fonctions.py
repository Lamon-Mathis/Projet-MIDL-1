from syntax import *
import sys
import itertools # Utilisé pour le produit cartésien dans la DNF

#=======================================================================    
# Fonctions utilitaires (Affichage, Dual, Eval)
#=======================================================================
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

def dualOp (formula: Formula):
    if isinstance(formula, BoolOpF):
        new_op = Disj() if isinstance(formula.op, Conj) else Conj()
        return BoolOpF(new_op, formula.elements)
    raise ValueError("type of formula is not allowed")

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
        if isinstance(formula.op, Conj):
            return all(eval(e) for e in formula.elements)
        else:
            return any(eval(e) for e in formula.elements)
    else :
        raise ValueError("Formula with quantifiers is not allowed")

#=======================================================
# ÉTAPE 0 : Pré-traitement
# Élimination des quantificateurs universels
#=======================================================    
def remove_forall(f: Formula) -> Formula:
    """Convertit ∀x.P en ¬(∃x.¬P)."""
    
    if isinstance(f, QuantifF):
        if isinstance(f.q, All):
            recurse_body = remove_forall(f.body)
            return NotF(QuantifF(Ex(), f.var, NotF(recurse_body)))
        else:
            return QuantifF(f.q, f.var, remove_forall(f.body))
            
    elif isinstance(f, BoolOpF):
        return BoolOpF(f.op, [remove_forall(e) for e in f.elements])
        
    elif isinstance(f, NotF):
        return NotF(remove_forall(f.sub))
        
    return f

#=======================================================
# ÉTAPES 1 & 2 : Forme Normale Négative Complète (contien la fonction nnf)
# - Tire les négations (NNF)
# - Élimine les négations devant les relations (¬< devient ≥)
#=======================================================
def push_negation(f: Formula) -> Formula:
    """
    Pousse les négations vers les feuilles et élimine les négations de relations.
    Cette fonction réalise les ÉTAPES 1 et 2 de l'algorithme.
    """
    if isinstance(f, NotF):
        sub = f.sub

        if isinstance(sub, ConstF):
            return ConstF(not sub.val)
            
        elif isinstance(sub, NotF): # not not
            return push_negation(sub.sub)
            
        elif isinstance(sub, BoolOpF):# not a or b
            new_op = Disj() if isinstance(sub.op, Conj) else Conj()
            new_elements = [push_negation(NotF(e)) for e in sub.elements]
            return BoolOpF(new_op, new_elements)
            
        elif isinstance(sub, ComparF):
            x = sub.left
            y = sub.right
            
            if isinstance(sub.op, Lt): # not (a < b)
                return disj(ltf(y, x), eqf(x, y))
                
            elif isinstance(sub.op, Eq): # not (a = b)
                return disj(ltf(x, y), ltf(y, x))
        
        elif isinstance(sub, QuantifF): # forall / exist
            new_q = All() if isinstance(sub.q, Ex) else Ex()
            return QuantifF(new_q, sub.var, push_negation(NotF(sub.body)))

    elif isinstance(f, BoolOpF):
        return BoolOpF(f.op, [push_negation(e) for e in f.elements])
        
    elif isinstance(f, QuantifF):
        return QuantifF(f.q, f.var, push_negation(f.body))

    return f

#=======================================================
# ÉTAPE 3 : Transformation en Liste DNF
#=======================================================
def to_dnf_list(f: Formula) -> list[list[Formula]]:
    """
    Transforme une formule sans quantificateurs en une liste de listes de littéraux.
    [[A, B], [C]] signifie (A ∧ B) ∨ C.
    Hypothèse: f est déjà traitée par push_negation (NNF + Relation).
    """
    if isinstance(f, ConstF):
        return [[f]] if f.val else []
        
    elif isinstance(f, ComparF):
        return [[f]]
        
    elif isinstance(f, BoolOpF):
        subs_dnf = [to_dnf_list(e) for e in f.elements]
        
        if isinstance(f.op, Disj): # a, b ou c
            return [clause for d in subs_dnf for clause in d]
            
        elif isinstance(f.op, Conj): # a ou b et c ou d
            product = itertools.product(*subs_dnf)
            result = []
            for combination in product:
                merged_clause = []
                for clause in combination:
                    merged_clause.extend(clause)
                result.append(merged_clause)
            return result
    return [[f]]

#=======================================================
# ÉTAPE 4 : Élimination de la quantification
# Partie A : Élimination dans une conjonction
#=======================================================
def eliminate_existential(var: str, conjunction: list[Formula]) -> Formula:
    """
    Élimine ∃var d'une conjonction de littéraux (ComparF ou ConstF).
    Retourne une formule équivalente sans 'var'.
    """
    lower_bounds = [] # u < x
    upper_bounds = [] # x < v
    equalities = []   # x = w (ou w = x)
    others = []       # formules ne contenant pas x
    
    for f in conjunction:
        if isinstance(f, ConstF):
            if not f.val: return ConstF(False) # Faux dans un ET annule tout
            continue # Vrai dans un ET est neutre
            
        if not isinstance(f, ComparF):
            others.append(f) # Cas de sécurité
            continue

        l, r = f.left, f.right
        
        # x < x impossible
        if l == var and r == var and isinstance(f.op, Lt):
            return ConstF(False)
        
        if isinstance(f.op, Eq):
            if l == var: equalities.append(r)
            elif r == var: equalities.append(l)
            else: others.append(f)
        elif isinstance(f.op, Lt):
            if l == var: upper_bounds.append(r) # var < r
            elif r == var: lower_bounds.append(l) # l < var
            else: others.append(f)

    # Cas avec égalité : x = w0
    if equalities:
        w0 = equalities[0]
        new_constraints = []
        
        # w = w0
        for w in equalities[1:]:
            new_constraints.append(eqf(w, w0))
        # u < w0
        for u in lower_bounds:
            new_constraints.append(ltf(u, w0))
        # w0 < v
        for v in upper_bounds:
            new_constraints.append(ltf(w0, v))
            
        final_list = new_constraints + others
        if not final_list: return ConstF(True)
        
        res = final_list[0]
        for item in final_list[1:]:
            res = conj(res, item)
        return res

    # Cas dense : bornes inf et sup -> on connecte u < v
    if lower_bounds and upper_bounds:
        new_constraints = []
        for u in lower_bounds:
            for v in upper_bounds:
                new_constraints.append(ltf(u, v))
        
        final_list = new_constraints + others
        if not final_list: return ConstF(True)
        
        res = final_list[0]
        for item in final_list[1:]:
            res = conj(res, item)
        return res

    # Cas semi-borné ou non borné : toujours vrai dans DLO
    if not others:
        return ConstF(True)
    
    res = others[0]
    for item in others[1:]:
        res = conj(res, item)
    return res

#=======================================================
# ÉTAPE 4 : Élimination de la quantification
# Partie B : Fonction principale récursive
#=======================================================
def process_formula(f: Formula) -> Formula:
    """Fonction principale pour éliminer les quantificateurs (Steps 1-4 intégrés)."""
    
    # 1. Traitement récursif des sous-formules
    # On élimine d'abord les quantificateurs dans les enfants (inside-out)
    if isinstance(f, BoolOpF):
        # Correction ici : BoolOpF utilise .elements, pas .left/.right
        new_elements = [process_formula(e) for e in f.elements]
        return BoolOpF(f.op, new_elements)
        
    elif isinstance(f, NotF):
        return NotF(process_formula(f.sub))
        
    # 2. Si on tombe sur un ∃, on applique l'élimination
    elif isinstance(f, QuantifF) and isinstance(f.q, Ex):
        
        # Le corps a déjà été traité récursivement (donc plus de quantificateurs imbriqués)
        body_processed = process_formula(f.body)
        
        # Étape 1 & 2 : NNF et Push Negation
        body_nnf = push_negation(body_processed)
        
        # Étape 3 : Mise en DNF (Liste de listes)
        dnf_clauses = to_dnf_list(body_nnf)
        
        # Étape 4 : Distribution de ∃ sur le OU
        results = []
        for clause in dnf_clauses:
            # Élimination de la variable pour chaque clause
            eliminated = eliminate_existential(f.var, clause)
            results.append(eliminated)
        
        # Reconstruction du résultat final (Disjonction des résultats)
        if not results:
            return ConstF(False)
            
        final_f = results[0]
        for res in results[1:]:
            final_f = disj(final_f, res)
            
        return final_f

    # Cas de base (Const, Compar, ou QuantifF All si remove_forall a échoué/pas été appelé)
    return f