# fonctions.py
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
# @brief cette fonction evalue une une formule sans quantificateurs (attention aux comparaisons)
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

# -----------------------------------------------------------------------------
# 1. Fonctions utilitaires et de parcours
# -----------------------------------------------------------------------------

def get_free_vars(f: Formula) -> set[str]:
    """Retourne l'ensemble des variables libres."""
    if isinstance(f, ConstF):
        return set()
    elif isinstance(f, ComparF):
        return {f.left, f.right}
    elif isinstance(f, NotF):
        return get_free_vars(f.sub)
    elif isinstance(f, BoolOpF):
        res = set()
        for sub_f in f.elements:
            res |= get_free_vars(sub_f)
        return res
    elif isinstance(f, QuantifF):
        return get_free_vars(f.body) - {f.var}
    return set()

def substitute_var(f: Formula, old_name: str, new_name: str) -> Formula:
    """Remplace old_name par new_name dans la formule."""
    if isinstance(f, ConstF):
        return f
    elif isinstance(f, ComparF):
        l = new_name if f.left == old_name else f.left
        r = new_name if f.right == old_name else f.right
        return ComparF(l, f.op, r)
    elif isinstance(f, NotF):
        return NotF(substitute_var(f.sub, old_name, new_name))
    elif isinstance(f, BoolOpF):
        new_elements = [substitute_var(e, old_name, new_name) for e in f.elements]
        return BoolOpF(f.op, new_elements)
    elif isinstance(f, QuantifF):
        if f.var == old_name:
            return f
        else:
            return QuantifF(f.q, f.var, substitute_var(f.body, old_name, new_name))
    return f

def get_precedence(f: Formula) -> int:
    """Retourne la priorité d'un opérateur sous forme de chiffre, plus il est haut plus c'est prioritaire"""
    if isinstance(f,(ConstF,ComparF)):
        return 5
    elif isinstance(f, NotF):
        return 4
    elif isinstance(f, BoolOpF):
        return 3 if isinstance(f.op, Conj) else 2 #ET est prioritaire sur le OU
    elif isinstance(f, QuantifF):
        return 1
    return 0

def min_parentheses(f: Formula, parent_prec: int=0) -> str:
    """Affiche une formule avec un parenthésage minimal"""

    current_prec = get_precedence(f)

    need_parens = current_prec < parent_prec

    if isinstance(f, ConstF):
        return "⊤" if f.val else "⊥"

    elif isinstance(f, ComparF):
        return f"{f.left}{f.op}{f.right}"

    elif isinstance(f, NotF):
        res = min_parentheses(f.sub,current_prec)
        return f"¬{res}"

    elif isinstance(f, BoolOpF):
        symbol = " ∧ " if isinstance(f.op, Conj) else " ∨ "

        # On récupère les enfants
        children_str = []
        for child in f.elements:

            child_prec = get_precedence(child)

            if child_prec < current_prec:
                children_str.append(f"({min_parentheses(child, 0)})")
            else:
                children_str.append(min_parentheses(child, current_prec))

        res = symbol.join(children_str)
        return f"({res})" if need_parens else res

    elif isinstance(f, QuantifF):
        res = f"{f.q}{f.var}.{min_parentheses(f.body, current_prec)}"
        return f"({res})" if need_parens else res

    return str(f)

# -----------------------------------------------------------------------------
# 2. Hypothèses (Annexe A.2.1)
# -----------------------------------------------------------------------------

def is_closed(f: Formula) -> bool:
    """
    Vérifie l'hypothèse que la formule est close.
    Retourne True si l'ensemble des variables libres est vide.
    """
    return len(get_free_vars(f)) == 0


def close_formula(f: Formula) -> Formula:
    """
    Ferme automatiquement la formule en ajoutant des quantificateurs universels
    pour toutes les variables libres trouvées.
    Exemple: (x < y) devient ∀x∀y.(x < y)
    """
    frees = get_free_vars(f)
    if not frees:
        return f

    # On trie pour avoir un ordre déterministe (x, puis y...)
    sorted_vars = sorted(list(frees))

    res = f
    for v in sorted_vars:
        res = allq(v, res)

    return res


# -----------------------------------------------------------------------------
#  3.Prétraitement
# -----------------------------------------------------------------------------

def remove_forall(f: Formula) -> Formula:
    """Convertit ∀x.P en ¬(∃x.¬P)."""
    if isinstance(f, QuantifF):
        if isinstance(f.q, All):
            return NotF(exq(f.var, NotF(remove_forall(f.body))))
        else:
            return QuantifF(f.q, f.var, remove_forall(f.body))
    elif isinstance(f, BoolOpF):
        new_elements = [remove_forall(e) for e in f.elements]
        return BoolOpF(f.op, new_elements)
    elif isinstance(f, NotF):
        return NotF(remove_forall(f.sub))
    return f

def push_negation(f: Formula) -> Formula:
    """Pousse les négations vers les feuilles."""
    if isinstance(f, NotF):
        sub = f.sub
        if isinstance(sub, ConstF):
            return ConstF(not sub.val)
        elif isinstance(sub, NotF):
            return push_negation(sub.sub)
        elif isinstance(sub, BoolOpF):
            new_op = Disj() if isinstance(sub.op, Conj) else Conj()
            new_elements = [push_negation(NotF(e)) for e in sub.elements]
            return BoolOpF(new_op, new_elements)
        elif isinstance(sub, ComparF):
            x, y = sub.left, sub.right
            if isinstance(sub.op, Lt):
                return disj(ltf(y, x), eqf(x, y))
            elif isinstance(sub.op, Eq):
                return disj(ltf(x, y), ltf(y, x))
            
        return f # Cas par défaut (ex: negation sur quantifieur)

    elif isinstance(f, BoolOpF):
        new_elements = [push_negation(e) for e in f.elements]
        return BoolOpF(f.op, new_elements)
    
    elif isinstance(f, QuantifF):
        return QuantifF(f.q, f.var, push_negation(f.body))
    
    return f

def to_prenex(f: Formula) -> Formula:
    """
    Forme Prénexe adaptée à la structure BoolOpF([A, B]).
    """
    if isinstance(f, NotF):
        sub = to_prenex(f.sub)
        if isinstance(sub, QuantifF):
            new_q = Ex() if isinstance(sub.q, All) else All()
            return to_prenex(QuantifF(new_q, sub.var, NotF(sub.body)))
        return NotF(sub)

    elif isinstance(f, BoolOpF):
        # On traite d'abord récursivement les enfants
        processed_elements = [to_prenex(e) for e in f.elements]
        
        if len(processed_elements) == 2: #opérateur binaire donc élément gauche et élément droite
            left, right = processed_elements[0], processed_elements[1]
            
            # Cas 1 : Quantificateur à Gauche (∃x.P) op R -> ∃x.(P op R)
            if isinstance(left, QuantifF):
                var, body = left.var, left.body
                if var in get_free_vars(right):
                    new_var = var + "'"
                    while new_var in get_free_vars(right) or new_var in get_free_vars(body):
                        new_var += "'"
                    body = substitute_var(body, var, new_var)
                    var = new_var
                
                # On reconstruit avec la nouvelle variable et le corps modifié
                return to_prenex(QuantifF(left.q, var, BoolOpF(f.op, [body, right])))

            # Cas 2 : Quantificateur à Droite L op (∃x.P) -> ∃x.(L op P)
            elif isinstance(right, QuantifF):
                var, body = right.var, right.body
                if var in get_free_vars(left):
                    new_var = var + "'"
                    while new_var in get_free_vars(left) or new_var in get_free_vars(body):
                        new_var += "'"
                    body = substitute_var(body, var, new_var)
                    var = new_var
                
                return to_prenex(QuantifF(right.q, var, BoolOpF(f.op, [left, body])))
            
            return BoolOpF(f.op, [left, right])
        
        return BoolOpF(f.op, processed_elements)

    elif isinstance(f, QuantifF):
        return QuantifF(f.q, f.var, to_prenex(f.body))

    return f

# -----------------------------------------------------------------------------
# 4. DNF et Élimination
# -----------------------------------------------------------------------------

def to_dnf_list(f: Formula) -> list[list[Formula]]:
    """Transforme en DNF (liste de listes)."""
    if isinstance(f, ConstF):
        return [[f]] if f.val else []
    elif isinstance(f, ComparF):
        return [[f]]
    elif isinstance(f, BoolOpF):
        # On suppose binaire car issu de conj/disj
        if len(f.elements) >= 2:
            left_dnf = to_dnf_list(f.elements[0])
            right_dnf = to_dnf_list(f.elements[1]) 
            
            if isinstance(f.op, Disj):
                return left_dnf + right_dnf
            elif isinstance(f.op, Conj):
                result = []
                for l_clause in left_dnf:
                    for r_clause in right_dnf:
                        result.append(l_clause + r_clause)
                return result
    return [[f]]

def eliminate_existential(var: str, conjunction: list[Formula]) -> Formula:
    lower, upper, equalities, others = [], [], [], []
    
    for f in conjunction:
        if isinstance(f, ConstF):
            if not f.val: return ConstF(False)
            continue
        if not isinstance(f, ComparF):
            others.append(f)
            continue

        l, r = f.left, f.right
        if l == var and r == var and isinstance(f.op, Lt): return ConstF(False)
        
        if isinstance(f.op, Eq):
            if l == var: equalities.append(r)
            elif r == var: equalities.append(l)
            else: others.append(f)
        elif isinstance(f.op, Lt):
            if l == var: upper.append(r)
            elif r == var: lower.append(l)
            else: others.append(f)

    if equalities:
        w0 = equalities[0]
        new_c = []
        for w in equalities[1:]: new_c.append(eqf(w, w0))
        for u in lower: new_c.append(ltf(u, w0))
        for v in upper: new_c.append(ltf(w0, v))
        final = new_c + others
        if not final: return ConstF(True)
        res = final[0]
        for x in final[1:]: res = conj(res, x)
        return res

    if lower and upper:
        new_c = [ltf(u, v) for u in lower for v in upper]
        final = new_c + others
        if not final: return ConstF(True)
        res = final[0]
        for x in final[1:]: res = conj(res, x)
        return res

    if not others: return ConstF(True)
    res = others[0]
    for x in others[1:]: res = conj(res, x)
    return res

def process_formula(f: Formula) -> Formula:
    if isinstance(f, QuantifF) and isinstance(f.q, Ex):
        body_simp = process_formula(f.body)
        body_nnf = push_negation(body_simp)
        dnf_clauses = to_dnf_list(body_nnf)
        results = [eliminate_existential(f.var, c) for c in dnf_clauses]
        
        if not results: return ConstF(False)
        final = results[0]
        for r in results[1:]: final = disj(final, r)
        return final
        
    elif isinstance(f, NotF):
        return NotF(process_formula(f.sub))
    elif isinstance(f, BoolOpF):
        new_elems = [process_formula(e) for e in f.elements]
        return BoolOpF(f.op, new_elems)
    return f

def simplify_bool(f: Formula) -> Formula:
    if isinstance(f, BoolOpF):
        new_elems = [simplify_bool(e) for e in f.elements]
        if len(new_elems) == 2:
            l, r = new_elems[0], new_elems[1]
            if isinstance(f.op, Conj):
                if isinstance(l, ConstF): return r if l.val else ConstF(False)
                if isinstance(r, ConstF): return l if r.val else ConstF(False)
            elif isinstance(f.op, Disj):
                if isinstance(l, ConstF): return ConstF(True) if l.val else r
                if isinstance(r, ConstF): return ConstF(True) if r.val else l
        return BoolOpF(f.op, new_elems)
    elif isinstance(f, NotF):
        sub = simplify_bool(f.sub)
        if isinstance(sub, ConstF): return ConstF(not sub.val)
        return NotF(sub)
    return f

def solve_do(f: Formula) -> bool:
    # 0. Fermeture automatique
    free_v = get_free_vars(f)
    for v in sorted(list(free_v)):
        f = allq(v, f)

    # 1. Prénexe
    f = to_prenex(f)
    
    # 2. ∀ -> ∃
    f = remove_forall(f)
    
    # 3. Élimination
    f = process_formula(f)
    
    # 4. Simplification
    f = simplify_bool(f)
    
    if isinstance(f, ConstF):
        return f.val
    else:
        print(f"Attention: Formule non réduite: {f}")
        return False