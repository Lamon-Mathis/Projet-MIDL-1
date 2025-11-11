# test_fonctions.py

from fonctions import *
from syntax import *

#=======================================================================
# Tests de dualOp
#=======================================================================
list_formula = [
    BoolOpF(Conj(), [ltf("a","b"), eqf("c","d")]),
    BoolOpF(Disj(), [eqf("x","y"), ltf("y","z"), eqf("z","x")]),
    BoolOpF(Conj(), [BoolOpF(Conj(), [ltf("p","q"), eqf("q","r")]), ltf("r","s")]),
    eqf("a","b"),
    allq("x", eqf("x","x"))
]

print("\n________________ Tests dualOp ________________\n")
for i in range(len(list_formula)):
    formula = list_formula[i]
    print("TEST "+ str(i+1))
    try:
        print("Avant : " + display_formula(formula))
        print("Après : " + display_formula(dualOp(formula))+"\n")
    except Exception as e:
        
        print("Test dualOp - Attendu ERREUR :", e,"\n")

#=======================================================================
# Tests de dual
#=======================================================================

print("\n________________ Tests dual ________________\n")
for i in range(len(list_formula)):
    formula = list_formula[i]
    print("TEST "+ str(i+1))
    try:
        print("Avant : " + display_formula(formula))
        print("Après : " + display_formula(dual(formula))+"\n")
    except Exception as e:
        
        print("Test dual - Attendu ERREUR :", e,"\n")

#=======================================================================
# Tests de eval
#=======================================================================
list_formula = [
    ConstF(True),
    eqf("a","a"),
    eqf("a","b"),
    BoolOpF(Conj(), [ltf("a","b"), eqf("a","a")]),
    BoolOpF(Disj(), [eqf("p","q"), ltf("m","n")]),
    allq("x", ltf("x","y")),
]

print("\n________________ Tests eval ________________\n")
for i in range(len(list_formula)):
    formula = list_formula[i]
    print("TEST "+ str(i+1))
    try:
        print("Formule : " + display_formula(formula))
        print("Évaluation : " + str(eval(formula))+"\n")
    except Exception as e:
        
        print("Test eval - Attendu ERREUR :", e,"\n")

print("\n________________ Tests nnf et dnf ________________\n")
A = ComparF("A", Eq(), "B")
B = ComparF("B", Lt(), "C")

# Formules composées
f1 = NotF(NotF(A))                      # ¬(¬A)
f2 = NotF(BoolOpF(Conj(), [A, B]))     # ¬(A ∧ B)
f3 = BoolOpF(Disj(), [A, NotF(B)])     # A ∨ ¬B
f4 = BoolOpF(Conj(), [A, f3])          # A ∧ (A ∨ ¬B)

print("===== TEST NNF =====")
print("f1 =", display_formula(f1), "→", display_formula(nnf(f1)))
print("f2 =", display_formula(f2), "→", display_formula(nnf(f2)))
print("f3 =", display_formula(f3), "→", display_formula(nnf(f3)))
print("f4 =", display_formula(f4), "→", display_formula(nnf(f4)))

print("\n===== TEST DNF =====")
print("f1 =", display_formula(f1), "→", display_formula(dnf(f1)))
print("f2 =", display_formula(f2), "→", display_formula(dnf(f2)))
print("f3 =", display_formula(f3), "→", display_formula(dnf(f3)))
print("f4 =", display_formula(f4), "→", display_formula(dnf(f4)))

print("\n________________ Fin des tests ________________\n")



