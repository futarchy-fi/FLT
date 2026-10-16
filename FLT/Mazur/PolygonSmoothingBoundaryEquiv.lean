/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBoundaryLift

/-!
# Constructing node automorphisms from full Laurent substitutions

Explicit coefficient tests for the two substitutions and their inverses
construct mutually inverse node maps. The resulting automorphism retains
both complete original boundary maps, rather than only their closed reductions.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)
  (e f : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹])

/-- Four families of coefficient equalities for the two transformed original generators. -/
def BoundaryCompatible : Prop :=
  LaurentCompatible t (e (leftLaurentMap t (leftCoordinate t)))
      (f (precedingLaurentMap R t (leftCoordinate t))) ∧
    LaurentCompatible t (e (leftLaurentMap t (rightCoordinate t)))
      (f (precedingLaurentMap R t (rightCoordinate t)))

/-- Construct the whole node endomorphism from the original boundary substitutions. -/
def laurentBoundaryEnd (h : BoundaryCompatible t e f) : ChartRing t →ₐ[R] ChartRing t :=
  boundaryLift t t (e.toAlgHom.comp (leftLaurentMap t))
    (f.toAlgHom.comp (precedingLaurentMap R t)) h.1 h.2

/-- The first complete Laurent substitution is recovered on every original chart element. -/
theorem laurentBoundaryEnd_left (h : BoundaryCompatible t e f) (z : ChartRing t) :
    leftLaurentMap t (laurentBoundaryEnd t e f h z) = e (leftLaurentMap t z) :=
  DFunLike.congr_fun (leftLaurentMap_boundaryLift t t
    (e.toAlgHom.comp (leftLaurentMap t))
    (f.toAlgHom.comp (precedingLaurentMap R t)) h.1 h.2) z

/-- The second complete Laurent substitution is recovered on every original chart element. -/
theorem laurentBoundaryEnd_preceding (h : BoundaryCompatible t e f) (z : ChartRing t) :
    precedingLaurentMap R t (laurentBoundaryEnd t e f h z) =
      f (precedingLaurentMap R t z) :=
  DFunLike.congr_fun (precedingLaurentMap_boundaryLift t t
    (e.toAlgHom.comp (leftLaurentMap t))
    (f.toAlgHom.comp (precedingLaurentMap R t)) h.1 h.2) z

/-- Inverse Laurent substitutions give an inverse on the entire original node. -/
theorem laurentBoundaryEnd_inverse (h : BoundaryCompatible t e f)
    (hi : BoundaryCompatible t e.symm f.symm) (z : ChartRing t) :
    laurentBoundaryEnd t e.symm f.symm hi (laurentBoundaryEnd t e f h z) = z := by
  apply pairedLaurent_ext t
  · rw [laurentBoundaryEnd_left, laurentBoundaryEnd_left, AlgEquiv.symm_apply_apply]
  · rw [laurentBoundaryEnd_preceding, laurentBoundaryEnd_preceding, AlgEquiv.symm_apply_apply]

/-- Both full node maps are constructed; their inverse laws follow from the branch equations. -/
def laurentBoundaryEquiv (h : BoundaryCompatible t e f)
    (hi : BoundaryCompatible t e.symm f.symm) : ChartRing t ≃ₐ[R] ChartRing t :=
  { laurentBoundaryEnd t e f h with
    invFun := laurentBoundaryEnd t e.symm f.symm hi
    left_inv := laurentBoundaryEnd_inverse t e f h hi
    right_inv := laurentBoundaryEnd_inverse t e.symm f.symm hi h }

/-- The constructed automorphism uses exactly the full outgoing substitution. -/
theorem laurentBoundaryEquiv_left (h : BoundaryCompatible t e f)
    (hi : BoundaryCompatible t e.symm f.symm) :
    (leftLaurentMap t).comp (laurentBoundaryEquiv t e f h hi).toAlgHom =
      e.toAlgHom.comp (leftLaurentMap t) :=
  leftLaurentMap_boundaryLift t t
    (e.toAlgHom.comp (leftLaurentMap t))
    (f.toAlgHom.comp (precedingLaurentMap R t)) h.1 h.2

/-- Its incoming square uses the same whole-chart automorphism. -/
theorem laurentBoundaryEquiv_preceding (h : BoundaryCompatible t e f)
    (hi : BoundaryCompatible t e.symm f.symm) :
    (precedingLaurentMap R t).comp (laurentBoundaryEquiv t e f h hi).toAlgHom =
      f.toAlgHom.comp (precedingLaurentMap R t) :=
  precedingLaurentMap_boundaryLift t t
    (e.toAlgHom.comp (leftLaurentMap t))
    (f.toAlgHom.comp (precedingLaurentMap R t)) h.1 h.2

/-- Extending the two substitutions requires exactly the stated generator coefficient tests. -/
theorem laurentBoundaryEnd_exists_iff :
    (∃ F : ChartRing t →ₐ[R] ChartRing t,
      (leftLaurentMap t).comp F = e.toAlgHom.comp (leftLaurentMap t) ∧
        (precedingLaurentMap R t).comp F = f.toAlgHom.comp (precedingLaurentMap R t)) ↔
      BoundaryCompatible t e f :=
  boundaryLift_exists_iff t t (e.toAlgHom.comp (leftLaurentMap t))
    (f.toAlgHom.comp (precedingLaurentMap R t))

end FLT.Mazur.PolygonSmoothing
