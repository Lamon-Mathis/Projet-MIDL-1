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
    """Retourne l'ensemble des variables libres d'une formule."""
    if isinstance(f, ConstF):
        return set()
    elif isinstance(f, ComparF):
        return {f.left, f.right}
    elif isinstance(f, NotF):
        return get_free_vars(f.sub)
    elif isinstance(f, BoolOpF):
        return get_free_vars(f.left) | get_free_vars(f.right)
    elif isinstance(f, QuantifF):
        return get_free_vars(f.body) - {f.var}
    return set()

def is_literal(f: Formula) -> bool:
    """Vérifie si la formule est un littéral (Comparaison ou Constante)."""
    return isinstance(f, ComparF) or isinstance(f, ConstF)

# -----------------------------------------------------------------------------
# 2. Prétraitement et Normalisation (Annexe A.2.2)
# -----------------------------------------------------------------------------

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
            # ¬(x < y) -> y < x ∨ x = y 
            # ¬(x = y) -> x < y ∨ y < x [cite: 269]
            x, y = sub.left, sub.right
            if isinstance(sub.op, Lt):
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

# -----------------------------------------------------------------------------
# 3. Élimination des variables (Annexe A.2.3)
# -----------------------------------------------------------------------------

def eliminate_existential(var: str, conjunction: list[Formula]) -> Formula:
    """
    Élimine ∃var d'une conjonction de littéraux (ComparF ou ConstF).
    Retourne une formule équivalente sans 'var'.
    """
    # 1. Si x n'est pas libre dans la conjonction -> return conjonction [cite: 276]
    # (On vérifie implicitement en triant les termes)
    
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
        
        # 2. Si x < x présent -> return False [cite: 277]
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

    # 4. Si égalité présente (x = w0) [cite: 279-280]
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

    # 5. Pas d'égalité, mais bornes inf ET sup présentes [cite: 281-282]
    # (∃x. u < x ∧ x < v) <-> u < v
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

    # 6. Uniquement bornes inf OU bornes sup (ou rien) [cite: 283]
    # L'ensemble est dense et sans bornes, donc on peut toujours trouver un x.
    # On supprime simplement les contraintes sur x.
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
    
    # Étape 1: Nettoyage (∀ -> ∃, NNF)
    # Note: On applique remove_forall au début globalement, mais ici on gère la récursion
    
    if isinstance(f, QuantifF) and isinstance(f.q, Ex):
        # On traite d'abord le corps (élimination de l'intérieur vers l'extérieur) [cite: 260]
        body_simplified = process_formula(f.body)
        
        # Étape 1 & 2 : NNF et Push Negation
        body_nnf = push_negation(body_processed)
        
        # Conversion en DNF : ∨ (∧ littéraux) 
        # ∃x. (C1 ∨ C2) <-> (∃x.C1) ∨ (∃x.C2) [cite: 272]
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

    elif isinstance(f, NotF):
        # Si on rencontre un Not après remove_forall, c'est souvent un ¬∃ (ancien ∀)
        # On traite récursivement
        return NotF(process_formula(f.sub))
        
    elif isinstance(f, BoolOpF):
        return BoolOpF(process_formula(f.left), f.op, process_formula(f.right))
        
    # Cas de base (Const, Compar)
    return f

# -----------------------------------------------------------------------------
# 4. Fonction Principale (Simplification finale)
# -----------------------------------------------------------------------------

def simplify_bool(f: Formula) -> Formula:
    """Simplification basique des constantes (True ∧ x -> x, etc.)."""
    if isinstance(f, BoolOpF):
        l = simplify_bool(f.left)
        r = simplify_bool(f.right)
        
        if isinstance(f.op, Conj):
            if isinstance(l, ConstF): return r if l.val else ConstF(False)
            if isinstance(r, ConstF): return l if r.val else ConstF(False)
        elif isinstance(f.op, Disj):
            if isinstance(l, ConstF): return ConstF(True) if l.val else r
            if isinstance(r, ConstF): return ConstF(True) if r.val else l
            
        return BoolOpF(l, f.op, r)
        
    elif isinstance(f, NotF):
        sub = simplify_bool(f.sub)
        if isinstance(sub, ConstF): return ConstF(not sub.val)
        return NotF(sub)
        
    return f

def solve_do(f: Formula) -> bool:
    """Procédure complète de décision."""
    # 1. ∀ -> ∃
    f_step1 = remove_forall(f)
    # 2. Élimination récursive
    f_step2 = process_formula(f_step1)
    # 3. Simplification booléenne finale
    f_final = simplify_bool(f_step2)
    
    print(f"Formule réduite : {f_final}")
    
    if isinstance(f_final, ConstF):
        return f_final.val
    else:
        # Si la formule n'est pas close ou si la simplification est incomplète
        raise ValueError("La formule n'a pas pu être réduite à un booléen (variables libres ?)")

# -----------------------------------------------------------------------------
# Exemple d'utilisation (basé sur le sujet)
# -----------------------------------------------------------------------------
if __name__ == "__main__":
    # Exemple 1 : ∀x.∀y.∀z. (x < y ∧ x < z -> y < z) (DO Confluence ?)
    # F1 dans le sujet[cite: 21]: ∀x∀y∀z (x<y ∧ x<z -> y<z) -> C'est Faux dans un ordre dense non linéaire, 
    # mais le sujet dit "elle décide si la formule est vraie (c'est le cas ici)". 
    # ATTENTION: Le sujet a une coquille ou parle d'un cas spécifique.
    # Dans DO (ordre total), x<y et x<z n'implique pas y<z (on peut avoir z<y).
    # Le sujet dit F1 = ∀x.∀y.∀z. (x < y ∧ x < z -> y < z). 
    # Testons une formule trivialement vraie pour DO : Transitivité ∀x,y,z (x<y ∧ y<z -> x<z)
    
    # Formule de test : ∃y (x < y ∧ y < z) (Densité entre x et z)
    # Cela devrait se réduire à x < z
    
    f_dense = exq("y", conj(ltf("x", "y"), ltf("y", "z")))
    print(f"Test Densité: {f_dense}")
    # Note: process_formula ne renvoie un bool que si la formule est close.
    # Pour tester solve_do, il faut une formule close.
    
    # Exemple Sujet Confluence corrigée : ∀x,y,z ∃u (x<y ∧ x<z -> y<u ∧ z<u)
    # C'est la propriété de confluence (dirigée).
    
    # Créons une formule simple close : ∃x (x < x) -> Faux
    f_false = exq("x", ltf("x", "x"))
    print(f"\nTest x < x (doit être False): {solve_do(f_false)}")
    
    # Créons une formule simple close : ∃x ∃y (x < y) -> Vrai (car sans extrema)
    f_true = exq("x", exq("y", ltf("x", "y")))
    print(f"Test ∃x ∃y x < y (doit être True): {solve_do(f_true)}")