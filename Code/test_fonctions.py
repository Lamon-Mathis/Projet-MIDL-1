# test_fonctions_new.py

from fonctions import *
from syntax import *

#=======================================================================
# 0. Tests de remove_forall (Pré-traitement)
#=======================================================================
list_forall = [
    allq("x", ltf("x", "y")),                       # ∀x. x < y
    allq("x", allq("y", eqf("x", "y"))),            # ∀x.∀y. x = y
    BoolOpF(Conj(), [allq("z", ltf("z","a")), eqf("a","b")]), # (∀z. z < a) ∧ a = b
    NotF(allq("x", ltf("x", "0")))                  # ¬∀x. x < 0
]

print("\n________________ Tests remove_forall (Etape 0) ________________\n")
for i in range(len(list_forall)):
    formula = list_forall[i]
    print("TEST "+ str(i+1))
    try:
        print("Avant : " + display_formula(formula))
        print("Après : " + display_formula(remove_forall(formula))+"\n")
    except Exception as e:
        print("Test remove_forall - Attendu ERREUR :", e,"\n")

#=======================================================================
# 1 & 2. Tests de push_negation (NNF + Négation Relations)
#=======================================================================
# On teste ici la descente des négations ET la transformation des relations
# ¬(x < y) devient (y < x ∨ x = y)
# ¬(x = y) devient (x < y ∨ y < x)
list_neg = [
    NotF(ltf("x", "y")),                            # ¬(x < y)
    NotF(eqf("a", "b")),                            # ¬(a = b)
    NotF(BoolOpF(Conj(), [ltf("x","a"), ltf("b","x")])), # ¬(x < a ∧ b < x) (De Morgan)
    NotF(NotF(ltf("x", "y"))),                      # ¬¬(x < y)
    push_negation(NotF(allq("x", ltf("x","y"))))    # Test sur un quantificateur inversé
]

print("\n________________ Tests push_negation (Etape 1 & 2) ________________\n")
for i in range(len(list_neg)):
    formula = list_neg[i]
    print("TEST "+ str(i+1))
    try:
        print("Avant : " + display_formula(formula))
        print("Après : " + display_formula(push_negation(formula))+"\n")
    except Exception as e:
        print("Test push_negation - Attendu ERREUR :", e,"\n")

#=======================================================================
# 3. Tests de to_dnf_list (Mise en DNF structurelle)
#=======================================================================
# Note : Ces formules doivent déjà être en NNF (pas de Not devant des parents)
list_dnf = [
    BoolOpF(Conj(), [                               # (A ∨ B) ∧ C
        BoolOpF(Disj(), [ltf("x","a"), eqf("x","b")]), 
        ltf("c","d")
    ]),
    BoolOpF(Conj(), [                               # (A ∨ B) ∧ (C ∨ D) -> Distrib
        BoolOpF(Disj(), [ltf("u","v"), eqf("u","v")]), 
        BoolOpF(Disj(), [ltf("x","y"), eqf("x","y")])
    ])
]

print("\n________________ Tests to_dnf_list (Etape 3) ________________\n")
for i in range(len(list_dnf)):
    formula = list_dnf[i]
    print("TEST "+ str(i+1))
    try:
        print("Formule : " + display_formula(formula))
        
        # Appel de la fonction
        res_list = to_dnf_list(formula)
        
        # Formatage manuel pour l'affichage (car c'est une liste de listes)
        str_res = " ∨ ".join([
            "(" + " ∧ ".join([display_formula(f) for f in clause]) + ")" 
            for clause in res_list
        ])
        print("DNF Liste : " + str_res + "\n")
        
    except Exception as e:
        print("Test to_dnf_list - Attendu ERREUR :", e,"\n")

#=======================================================================
# 4. Tests de process_formula (Résolution / Elimination complète)
#=======================================================================
# C'est ici qu'on teste si l'élimination des quantificateurs fonctionne
list_process = [
    # Cas 1 : Densité -> ∃x. (a < x ∧ x < b)  => a < b
    exq("x", BoolOpF(Conj(), [ltf("a", "x"), ltf("x", "b")])),
    
    # Cas 2 : Égalité -> ∃x. (x = z ∧ x < b) => z < b
    exq("x", BoolOpF(Conj(), [eqf("x", "z"), ltf("x", "b")])),
    
    # Cas 3 : Contradiction -> ∃x. (x < x) => ⊥
    exq("x", ltf("x", "x")),
    
    # Cas 4 : Unbounded -> ∃x. (a < x) => ⊤ (car dense sans fin)
    exq("x", ltf("a", "x")),
    
    # Cas 5 : Complexe avec OU -> ∃x. ((x=a) ∨ (x < b ∧ b < x))
    exq("x", BoolOpF(Disj(), [
        eqf("x", "a"), 
        BoolOpF(Conj(), [ltf("x", "b"), ltf("b", "x")])
    ]))
]

print("\n________________ Tests process_formula (Etape 4 - Final) ________________\n")
for i in range(len(list_process)):
    formula = list_process[i]
    print("TEST "+ str(i+1))
    try:
        print("Entrée : " + display_formula(formula))
        res = process_formula(formula)
        print("Sortie (Sans ∃) : " + display_formula(res) + "\n")
    except Exception as e:
        print("Test process_formula - Attendu ERREUR :", e,"\n")

print("\n________________ Fin des tests ________________\n")