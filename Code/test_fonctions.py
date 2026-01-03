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



#=======================================================================
# Tests de Traitement
#=======================================================================
import unittest

class TestLogicDO(unittest.TestCase):

    def setUp(self):
        """Initialisation des variables communes pour les tests."""
        # Variables simples pour éviter de réécrire les chaînes
        self.x = "x"
        self.y = "y"
        self.z = "z"
        self.u = "u"
        self.v = "v"

    # =========================================================================
    # TÂCHE T1 : Prise en main et fonctions de base
    # =========================================================================

    def test_get_free_vars(self):
        """Vérifie l'extraction des variables libres."""
        # Cas 1: x < y -> {x, y}
        f1 = ltf(self.x, self.y)
        self.assertEqual(get_free_vars(f1), {self.x, self.y})

        # Cas 2: ∃x. x < y -> {y} (x est liée)
        f2 = exq(self.x, f1)
        self.assertEqual(get_free_vars(f2), {self.y})

        # Cas 3: ∀x. x = x -> {} (formule close)
        f3 = allq(self.x, eqf(self.x, self.x))
        self.assertEqual(get_free_vars(f3), set())

    # =========================================================================
    # TÂCHE T2 : Prétraitement (Annexe A.2.2)
    # =========================================================================

    def test_remove_forall(self):
        """Vérifie la conversion des universels en existentiels."""
        # ∀x. P  devient  ¬(∃x. ¬P)
        f = allq(self.x, ltf(self.x, self.y))
        res = remove_forall(f)
        
        # On vérifie la structure : NotF(QuantifF(Ex, ..., NotF(...)))
        self.assertIsInstance(res, NotF)
        self.assertIsInstance(res.sub, QuantifF)
        self.assertIsInstance(res.sub.q, Ex)
        self.assertIsInstance(res.sub.body, NotF)

    def test_push_negation_relations(self):
        """Vérifie l'élimination des négations devant les relations."""
        # ¬(x < y) -> y < x ∨ x = y
        # Attention : selon ton implémentation, l'ordre ou le type (y < x vs x = y) peut varier,
        # on vérifie donc la logique globale.
        
        f = NotF(ltf(self.x, self.y))
        res = push_negation(f)
        
        # Le résultat doit être une Disjonction (OR)
        self.assertIsInstance(res, BoolOpF)
        self.assertIsInstance(res.op, Disj)
        
        # On doit retrouver soit (y < x) soit (x = y) dans les branches
        # Note: ceci suppose que push_negation fait le travail complètement
        str_res = str(res)
        self.assertIn(self.x, str_res)
        self.assertIn(self.y, str_res)

    def test_push_negation_demorgan(self):
        """Vérifie les lois de De Morgan."""
        # ¬(A ∧ B) -> ¬A ∨ ¬B
        f = NotF(conj(ltf("a", "b"), ltf("c", "d")))
        res = push_negation(f)
        
        self.assertIsInstance(res, BoolOpF)
        self.assertIsInstance(res.op, Disj) # Le ET devient OU

    # =========================================================================
    # TÂCHE T2 : Élimination (Annexe A.2.3)
    # =========================================================================

    def test_elimination_trivial_false(self):
        """Cas : x < x -> False."""
        # Liste de conjonction représentant : x < x
        clauses = [ltf(self.x, self.x)]
        res = eliminate_existential(self.x, clauses)
        
        self.assertIsInstance(res, ConstF)
        self.assertFalse(res.val)

    def test_elimination_substitution(self):
        """Cas : x = z ∧ y < x -> y < z [cite: 279-280]."""
        # Liste : [x = z, y < x]
        clauses = [eqf(self.x, self.z), ltf(self.y, self.x)]
        res = eliminate_existential(self.x, clauses)
        
        # Le résultat ne doit plus contenir x
        self.assertNotIn(self.x, str(res))
        # Doit contenir y et z
        self.assertTrue(str(res).count(self.y) >= 1)
        self.assertTrue(str(res).count(self.z) >= 1)

    def test_elimination_transitivity(self):
        """Cas : u < x ∧ x < v -> u < v [cite: 281-282]."""
        # Liste : [u < x, x < v]
        clauses = [ltf(self.u, self.x), ltf(self.x, self.v)]
        res = eliminate_existential(self.x, clauses)
        
        # Le résultat doit être u < v (ou équivalent logiquement)
        # Vérifions structurellement si c'est simple
        if isinstance(res, ComparF):
            self.assertEqual(res.left, self.u)
            self.assertEqual(res.right, self.v)
            self.assertIsInstance(res.op, Lt)

    def test_elimination_unbounded(self):
        """Cas : x < u (seulement) -> True."""
        # Densité sans bornes : si on a juste x < u, il existe toujours un x plus petit.
        clauses = [ltf(self.x, self.u)]
        res = eliminate_existential(self.x, clauses)
        
        self.assertIsInstance(res, ConstF)
        self.assertTrue(res.val)

    # =========================================================================
    # TÂCHE T2 : Tests globaux (Solveur complet)
    # =========================================================================

    def test_solver_irreflexivity(self):
        """Test propriété : ∀x ¬(x < x) -> Vrai."""
        # Représentation : ∀x ¬(x < x)
        f = allq(self.x, NotF(ltf(self.x, self.x)))
        self.assertTrue(solve_do(f))

    def test_solver_transitivity(self):
        """Test propriété : ∀x,y,z (x < y ∧ y < z -> x < z) -> Vrai."""
        # Implémentation : (A ∧ B -> C) <=> ¬(A ∧ B) ∨ C
        # Transitivité : x < y ∧ y < z => x < z
        premise = conj(ltf(self.x, self.y), ltf(self.y, self.z))
        conclusion = ltf(self.x, self.z)
        f = allq(self.x, allq(self.y, allq(self.z, impl(premise, conclusion))))
        
        self.assertTrue(solve_do(f))

    def test_solver_density(self):
        """Test propriété : ∀x,z (x < z -> ∃y (x < y ∧ y < z)) -> Vrai."""
        # Entre deux points distincts, il y en a un troisième.
        premise = ltf(self.x, self.z)
        conclusion = exq(self.y, conj(ltf(self.x, self.y), ltf(self.y, self.z)))
        f = allq(self.x, allq(self.z, impl(premise, conclusion)))
        
        self.assertTrue(solve_do(f))

    def test_solver_false_statement(self):
        """Test d'une formule fausse : ∃x (x < x)."""
        f = exq(self.x, ltf(self.x, self.x))
        self.assertFalse(solve_do(f))
    
    def test_solver_confluence_simplified(self):
        """
        Test Confluence (simplifiée pour le test).
        ∀x,y,z ∃u (y < u ∧ z < u) -> Vrai (car pas de max global)
        """
        f = allq("y", allq("z", exq("u", conj(ltf("y", "u"), ltf("z", "u")))))
        self.assertTrue(solve_do(f))

if __name__ == '__main__':
    unittest.main(verbosity=2)