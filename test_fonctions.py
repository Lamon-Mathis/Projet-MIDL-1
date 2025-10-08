# test_fonctions.py

from fonctions import *
from syntax import *

"""
La plus grande partie de ces test sont ecrit avec Copilot    """

#======================================================================
#   Tests de la fonction eval
#======================================================================
print("\n________________ Début des tests eval ________________\n")

# Test 1 : ¬(a < b) → (a = b ∨ b < a)
f1 = NotF(ltf("a", "b"))
print("Test 1 - Cas (a) avant :", f1)
print("Test 1 - Cas (a) après :", pretraitement(f1))
print("Test 1 - Évaluation :", eval(pretraitement(f1)))

# Test 2 : ⊤ ∧ ⊥
f2 = conj(ConstF(True), ConstF(False))
print("Test 2 - Formule :", f2)
print("Test 2 - Évaluation :", eval(f2))

# Test 3 : (a = a) ∨ (a < b)
f3 = disj(eqf("a", "a"), ltf("a", "b"))
print("Test 3 - Formule :", f3)
print("Test 3 - Évaluation :", eval(f3))

# Test 4 : ¬(a = b) → (a < b ∨ b < a)
f4 = NotF(eqf("a", "b"))
print("Test 4 - Cas (b) avant :", f4)
print("Test 4 - Cas (b) après :", pretraitement(f4))
print("Test 4 - Évaluation :", eval(pretraitement(f4)))

# Test 5 : ¬⊤
f5 = NotF(ConstF(True))
print("Test 5 - Formule :", f5)
print("Test 5 - Évaluation :", eval(f5))


#======================================================================
#   Tests de la fonction dualOp
#======================================================================
print("\n________________ Début des tests dualOp ________________\n")

op1 = Conj()
print("dualOp(∧) :", op1, "-->", dualOp(op1))

op2 = Disj()
print("dualOp(∨) :", op2, "-->", dualOp(op2))


#======================================================================
#   Tests de la fonction dual
#======================================================================
print("\n________________ Début des tests dual ________________\n")

# Cas 1 : ⊤
f1 = ConstF(True)
print("dual(⊤) :", f1, "-->", dual(f1))

# Cas 2 : (a = b)
f2 = eqf("a", "b")
print("dual(a = b) :", f2, "-->", dual(f2))

# Cas 3 : ¬(a < b)
f3 = NotF(ltf("a", "b"))
print("dual(¬(a < b)) :", f3, "-->", dual(f3))

# Cas 4 : (⊤ ∧ ⊥)
f4 = conj(ConstF(True), ConstF(False))
print("dual(⊤ ∧ ⊥) :", f4, "-->", dual(f4))

# Cas 5 : ((a = b) ∨ (b < c))
f5 = disj(eqf("a", "b"), ltf("b", "c"))
print("dual((a = b) ∨ (b < c)) :", f5, "-->", dual(f5))


#======================================================================
#   Tests de la fonction pretraitement
#======================================================================
print("\n________________ Début des tests pretraitement ________________\n")

# Cas (a) : ¬(a < b) ↔ (a = b ∨ b < a)
f1 = NotF(ltf("a", "b"))
print("Cas (a) :", f1, "-->", pretraitement(f1))

# Cas (b) : ¬(c = d) ↔ (c < d ∨ d < c)
f2 = NotF(eqf("c", "d"))
print("Cas (b) :", f2, "-->", pretraitement(f2))

# Cas imbriqué : ¬((e < f) ∧ (f < g))
f3 = NotF(conj(ltf("e", "f"), ltf("f", "g")))
print("Cas imbriqué :", f3, "-->", pretraitement(f3))

# Cas mixte : ¬((h = i) ∨ (h < j))
f4 = NotF(disj(eqf("h", "i"), ltf("h", "j")))
print("Cas mixte :", f4, "-->", pretraitement(f4))

# Cas booléen simple sans négation
f5 = conj(eqf("k", "l"), ltf("l", "m"))
print("Cas simple :", f5, "-->", pretraitement(f5))

