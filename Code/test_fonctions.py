# test_fonctions.py

from fonctions import *
from syntax import *

# Tests réécrits dans le format du premier test (avant / après / évaluation)

print("\n________________ Début des tests eval ________________\n")

# Test 1 : ¬(a < b) → (a = b ∨ b < a)
f1 = NotF(ltf("a", "b"))
f1_apres = pretraitement(f1)
print("Test 1 - Avant -> Après :", f1, "->", f1_apres)
print("Test 1 - Évaluation :", eval(f1_apres))

# Test 2 : ⊤ ∧ ⊥
f2 = conj(ConstF(True), ConstF(False))
print("Test 2 - Avant :", f2)
print("Test 2 - Évaluation :", eval(f2))

# Test 3 : (a = a) ∨ (a < b)
f3 = disj(eqf("a", "a"), ltf("a", "b"))
print("Test 3 - Avant :", f3)
print("Test 3 - Évaluation :", eval(f3))

# Test 4 : ¬(a = b) → (a < b ∨ b < a)
f4 = NotF(eqf("a", "b"))
f4_apres = pretraitement(f4)
print("Test 4 - Avant -> Après :", f4, "->", f4_apres)
print("Test 4 - Évaluation :", eval(f4_apres))

# Test 5 : ¬⊤
f5 = NotF(ConstF(True))
print("Test 5 - Avant :", f5)
print("Test 5 - Évaluation :", eval(f5))


print("\n________________ Début des tests dualOp ________________\n")

# dualOp tests (format: avant -> après)
op1 = Conj()
print("Test 6 - Avant -> Après :", op1, "->", dualOp(op1))

op2 = Disj()
print("Test 7 - Avant -> Après :", op2, "->", dualOp(op2))


print("\n________________ Début des tests dual ________________\n")

# dual tests (format: avant -> après)
d1 = ConstF(True)
print("Test 8 - Avant -> Après :", d1, "->", dual(d1))

d2 = eqf("a", "b")
print("Test 9 - Avant -> Après :", d2, "->", dual(d2))

d3 = NotF(ltf("a", "b"))
print("Test 10 - Avant -> Après :", d3, "->", dual(d3))

d4 = conj(ConstF(True), ConstF(False))
print("Test 11 - Avant -> Après :", d4, "->", dual(d4))

d5 = disj(eqf("a", "b"), ltf("b", "c"))
print("Test 12 - Avant -> Après :", d5, "->", dual(d5))


print("\n________________ Début des tests pretraitement ________________\n")

# Prétraitement : afficher avant -> après

p1 = NotF(ltf("a", "b"))
print("Test 13 - Avant -> Après :", p1, "->", pretraitement(p1))

p2 = NotF(eqf("c", "d"))
print("Test 14 - Avant -> Après :", p2, "->", pretraitement(p2))

p3 = NotF(conj(ltf("e", "f"), ltf("f", "g")))
print("Test 15 - Avant -> Après :", p3, "->", pretraitement(p3))

p4 = NotF(disj(eqf("h", "i"), ltf("h", "j")))
print("Test 16 - Avant -> Après :", p4, "->", pretraitement(p4))

p5 = conj(eqf("k", "l"), ltf("l", "m"))
print("Test 17 - Avant -> Après :", p5, "->", pretraitement(p5))

# Nouveaux cas (mêmes exemples que précédemment)
p6 = NotF(NotF(ltf("p", "q")))
print("Test 18 - Avant -> Après :", p6, "->", pretraitement(p6))

p7 = exq("x", ltf("x", "y"))
print("Test 19 - Avant -> Après :", p7, "->", pretraitement(p7))

p8 = exq("x", disj(ltf("x", "y"), ltf("y", "z")))
print("Test 20 - Avant -> Après :", p8, "->", pretraitement(p8))

p9 = exq("x", conj(ltf("x", "y"), eqf("y", "z")))
print("Test 21 - Avant -> Après :", p9, "->", pretraitement(p9))

p10 = exq("x", NotF(conj(eqf("x", "y"), ltf("y", "z"))))
print("Test 22 - Avant -> Après :", p10, "->", pretraitement(p10))

print("\n________________ Fin des tests pretraitement ________________\n")
