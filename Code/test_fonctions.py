# test_fonctions.py

from fonctions_bis import *
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



#=======================================================================
# Tests de Traitement
#=======================================================================
import unittest

print("\n________________ Tests Solveur (Eval) ________________\n")
# Test de solve_do (équivalent à eval)
list_solve = [
    # ∃x (x < x) -> Faux
    exq("x", ltf("x", "x")),

    # ∀x (x=x) -> Vrai (représenté par ¬∃x ¬(x=x))
    allq("x", eqf("x", "x")),

    # Densité: ∀x,z (x<z -> ∃y (x<y ∧ y<z)) -> Vrai
    allq("x", allq("z", impl(ltf("x", "z"), exq("y", conj(ltf("x", "y"), ltf("y", "z"))))))
]

for i in range(len(list_solve)):
    f = list_solve[i]
    print(f"TEST {i + 1}")
    try:
        print("Formule : " + str(f))
        print("Résultat : " + str(solve_do(f)) + "\n")
    except Exception as e:
        print("Test Solveur - ERREUR :", e, "\n")

# =======================================================================
# PARTIE 2 : Tests Unitaires (unittest)
# =======================================================================
print("\n________________ Lancement des Tests Unitaires ________________\n")


class TestLogicDO(unittest.TestCase):

    def setUp(self):
        """Initialisation des variables communes pour les tests."""
        self.x = "x"
        self.y = "y"
        self.z = "z"
        self.u = "u"
        self.v = "v"

    # --- TÂCHE T1 : Fonctions de base ---

    def test_get_free_vars(self):
        """Vérifie l'extraction des variables libres."""
        f1 = ltf(self.x, self.y)
        self.assertEqual(get_free_vars(f1), {self.x, self.y})

        f2 = exq(self.x, f1)
        self.assertEqual(get_free_vars(f2), {self.y})

        f3 = allq(self.x, eqf(self.x, self.x))
        self.assertEqual(get_free_vars(f3), set())


    # --- TÂCHE T2 : Convertion en forme prénexe ---
    def test_prenex_negation(self):
        """Test ¬∀x P -> ∃x ¬P"""
        # ¬(∀x. x < y) -> ∃x. ¬(x < y)
        f = NotF(allq(self.x, ltf(self.x, self.y)))
        res = to_prenex(f)
        
        self.assertIsInstance(res, QuantifF)
        self.assertIsInstance(res.q, Ex) # Devenu Ex
        self.assertIsInstance(res.body, NotF) # Le Not est descendu
        print("test_prenex_negation : OK")

    def test_prenex_conjunction(self):
        """Test remonter quantificateur dans un ET"""
        # (∀x. x = y) ∧ (z < u) -> ∀x. (x = y ∧ z < u)
        f = conj(allq(self.x, eqf(self.x, self.y)), ltf(self.z, self.u))
        res = to_prenex(f)
        
        self.assertIsInstance(res, QuantifF)
        self.assertIsInstance(res.q, All)
        self.assertIsInstance(res.body, BoolOpF)
        print("test_prenex_conjuction : OK")

    def test_prenex_collision(self):
        """Test renommage automatique si collision"""
        # (∀x. x < y) ∧ (x = z)
        # Ici x est lié à gauche, mais libre à droite.
        # On ne peut pas juste sortir le x. Il faut renommer le x de gauche.
        # Résultat attendu : ∀x'. (x' < y ∧ x = z)

        f = conj(allq(self.x, eqf(self.x, self.y)), ltf(self.z, self.u))
        
        res = to_prenex(f)
        print(f)
        
        # Le quantificateur doit être au sommet
        self.assertIsInstance(res, QuantifF)
        # La variable quantifiée ne doit PAS être 'x' (car x était libre à droite)
        self.assertEqual(res.var, self.x)
        # Le corps doit contenir la nouvelle variable ET l'ancienne x (celle de droite)
        s_res = str(res)
        self.assertTrue(self.x in s_res)

    # --- TÂCHE T2 : Prétraitement ---

    def test_remove_forall(self):
        """Vérifie la conversion ∀ -> ¬∃¬."""
        f = allq(self.x, ltf(self.x, self.y))
        res = remove_forall(f)
        self.assertIsInstance(res, NotF)
        self.assertIsInstance(res.sub, QuantifF)  # Doit être un ∃

    def test_push_negation_relations(self):
        """Vérifie ¬(x < y) -> y < x ∨ x = y."""
        f = NotF(ltf(self.x, self.y))
        res = push_negation(f)
        self.assertIsInstance(res, BoolOpF)
        self.assertIsInstance(res.op, Disj)  # OU
        s = str(res)
        self.assertTrue((self.x in s) and (self.y in s))

    # --- TÂCHE T2 : Élimination ---

    def test_elimination_trivial_false(self):
        """Cas : x < x -> False."""
        clauses = [ltf(self.x, self.x)]
        res = eliminate_existential(self.x, clauses)
        self.assertIsInstance(res, ConstF)
        self.assertFalse(res.val)

    def test_elimination_substitution(self):
        """Cas : x = z ∧ y < x -> y < z."""
        clauses = [eqf(self.x, self.z), ltf(self.y, self.x)]
        res = eliminate_existential(self.x, clauses)
        self.assertNotIn(self.x, str(res))  # x doit disparaitre

    def test_elimination_transitivity(self):
        """Cas : u < x ∧ x < v -> u < v."""
        clauses = [ltf(self.u, self.x), ltf(self.x, self.v)]
        res = eliminate_existential(self.x, clauses)
        # Vérif sommaire de la structure
        self.assertTrue(str(res).count(self.u) > 0)
        self.assertTrue(str(res).count(self.v) > 0)

    # --- TÂCHE T2 : Solveur Complet ---

    def test_solver_density(self):
        """Propriété de densité."""
        premise = ltf(self.x, self.z)
        conclusion = exq(self.y, conj(ltf(self.x, self.y), ltf(self.y, self.z)))
        f = allq(self.x, allq(self.z, impl(premise, conclusion)))
        self.assertTrue(solve_do(f))

    def test_solver_false_statement(self):
        """Formule fausse."""
        f = exq(self.x, ltf(self.x, self.x))
        self.assertFalse(solve_do(f))


if __name__ == '__main__':
    # unittest.main() va exécuter les tests de la classe TestLogicDO
    # et afficher le résumé à la fin.
    unittest.main(verbosity=2)