# fonctions.py

from syntax import *

#=======================================================================    
# fonction evaluation
#=======================================================================

def eval(f: Formula) -> bool:
    if isinstance(f, ConstF ):
        return f.val
    
    elif isinstance(f, ComparF ):
        if f.op == Eq():
            return (f.left == f.right)
        else :
            return (f.left != f.right)
        
    elif isinstance(f,NotF):
        return not eval(f.sub)
    
    elif isinstance(f,BoolOpF) :
        if isinstance(f.op,Conj):
            return (eval(f.left) and eval(f.right))
        else :
            return (eval(f.left) or eval(f.right))
    
    else :
        raise ValueError("Formule Quantifiée")

#=======================================================================    
# fonction dualOp et dual
#=======================================================================

def dualOp (op: BoolOp ) -> BoolOp :
    if isinstance (op , Conj ):
        return (Disj ())
    else:
        return (Conj ())
    
def dual(f: Formula ) -> Formula :
    if isinstance (f, ConstF ):
        return f
    elif isinstance (f, ComparF ):
        return f
    elif isinstance (f, NotF ):
        return NotF(dual(f.sub ))
    elif isinstance (f, BoolOpF ):
        return BoolOpF (dual(f.left), dualOp (f.op), dual(f. right ))
    else:
        raise ValueError ("dual applied to quantified formula ")

#=======================================================================    
# fonction pretraitement
#=======================================================================

def pretraitement(f: Formula) -> Formula:
    """
    Prétraitement d'une formule de la forme ∃x. φ :
    1. Tirer les négations à l'intérieur (forme normale négative)
        (1) ¬ a ^ b ↔ ¬a ∨ ¬b
        (2) ¬ a ∨ b ↔ ¬a ^ ¬b
    2. Éliminer les négations devant les relations :
       (a) ¬(z ≺ z') ↔ (z = z' ∨ z' ≺ z)
       (b) ¬(z = z') ↔ (z ≺ z' ∨ z' ≺ z)
    3. Transformer en forme normale disjonctive
    4. Tirer les quantificateurs à l’intérieur des disjonctions
    """
    
    # On se place aprés les quantificateurs
    while isinstance(f,QuantifF) :
        f = f.body
    
    if isinstance(f,NotF) :
        sub = f.sub

        # Cas (1) et (2)
        if isinstance(sub, BoolOpF):
            if isinstance(sub.op, Conj):
                return pretraitement(BoolOpF(NotF(sub.left), Disj(), NotF(sub.right)))
            elif isinstance(sub.op, Disj):
                return pretraitement(BoolOpF(NotF(sub.left), Conj(), NotF(sub.right)))

        # Cas (a) et (b)
        elif isinstance(sub, ComparF):
            if isinstance(sub.op, Lt):
                return BoolOpF(
                    ComparF(sub.left, Eq(), sub.right),
                    Disj(),
                    ComparF(sub.right, Lt(), sub.left)
                )
            elif isinstance(sub.op, Eq):
                return BoolOpF(
                    ComparF(sub.left, Lt(), sub.right),
                    Disj(),
                    ComparF(sub.right, Lt(), sub.left)
                )

        # Sinon, on continue à pousser la négation
        return NotF(pretraitement(sub))
        
        
        
    else :
        return ValueError("Formule inconnue pour le prétraitement.")
    
    
def pretraitementDeMerde(f: Formula) -> Formula:
    """
    Prétraitement d'une formule de la forme ∃x. φ :
    1. Tirer les négations à l'intérieur (forme normale négative)
    2. Éliminer les négations devant les relations :
       (a) ¬(z ≺ z') ↔ (z = z' ∨ z' ≺ z)
       (b) ¬(z = z') ↔ (z ≺ z' ∨ z' ≺ z)
    3. Transformer en forme normale disjonctive
    4. Tirer les quantificateurs à l’intérieur des disjonctions
    """

    # --- Cas atomiques ---
    if isinstance(f, ConstF) or isinstance(f, ComparF):
        return f

    # --- Cas des connecteurs booléens ---
    elif isinstance(f, BoolOpF):
        left = pretraitement(f.left)
        right = pretraitement(f.right)
        return BoolOpF(left, f.op, right)

    # --- Cas des négations ---
    elif isinstance(f, NotF):
        sub = f.sub

        # Lois de De Morgan : ¬(φ ∧ ψ) ↦ (¬φ ∨ ¬ψ)
        if isinstance(sub, BoolOpF):
            if isinstance(sub.op, Conj):
                return pretraitement(BoolOpF(NotF(sub.left), Disj(), NotF(sub.right)))
            elif isinstance(sub.op, Disj):
                return pretraitement(BoolOpF(NotF(sub.left), Conj(), NotF(sub.right)))

        # Cas (a) et (b)
        elif isinstance(sub, ComparF):
            if isinstance(sub.op, Lt):
                # ¬(z ≺ z') ↦ (z = z' ∨ z' ≺ z)
                return BoolOpF(
                    ComparF(sub.left, Eq(), sub.right),
                    Disj(),
                    ComparF(sub.right, Lt(), sub.left)
                )
            elif isinstance(sub.op, Eq):
                # ¬(z = z') ↦ (z ≺ z' ∨ z' ≺ z)
                return BoolOpF(
                    ComparF(sub.left, Lt(), sub.right),
                    Disj(),
                    ComparF(sub.right, Lt(), sub.left)
                )

        # Sinon, on continue à pousser la négation
        return NotF(pretraitement(sub))

    # --- Cas d'une quantification existentielle ---q
    elif isinstance(f, QuantifF):
        # Appliquer le prétraitement à la sous-formule
        inner = pretraitement(f.body)

        # Étape 3 : si inner est une disjonction, tirer la quantification à l’intérieur
        if isinstance(inner, BoolOpF) and isinstance(inner.op, Disj):
            return BoolOpF(
                exq(f.var, inner.left),
                Disj(),
                exq(f.var, inner.right)
            )

        return exq(f.var, inner)

    else:
        raise ValueError("Formule inconnue pour le prétraitement.")

