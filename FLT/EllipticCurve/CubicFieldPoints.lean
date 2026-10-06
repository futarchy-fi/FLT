/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicGlobalCommutativity

/-! # Classical points as points of the glued cubic -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluate the ordinary chart at any algebra-valued solution of the cubic equation. -/
def affineEvaluation {S : Type u} [CommRing S] [Algebra R S] (x y : S)
    (h : (W.map (algebraMap R S)).toAffine.Equation x y) : Ring W false →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W false}) (aeval ![x, y]) (by
    change Ideal.span {equation W false} ≤
      RingHom.ker (aeval ![x, y] : MvPolynomial (Fin 2) R →ₐ[R] S).toRingHom
    rw [Ideal.span_le]
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    change aeval ![x, y] (equation W false) = 0
    simpa [equation, Affine.equation_iff', WeierstrassCurve.map] using h)

@[simp] theorem affineEvaluation_coord {S : Type u} [CommRing S] [Algebra R S]
    (x y : S) (h : (W.map (algebraMap R S)).toAffine.Equation x y) (i : Fin 2) :
    affineEvaluation W x y h (coord W false i) = ![x, y] i := by
  change aeval ![x, y] (X i) = _
  simp

theorem affineEvaluation_neg {S : Type u} [CommRing S] [Algebra R S]
    (x y : S) (h : (W.map (algebraMap R S)).toAffine.Equation x y) :
    (affineEvaluation W x y h).comp (affineNegationEquiv W).toAlgHom =
      affineEvaluation W x ((W.map (algebraMap R S)).toAffine.negY x y)
        ((Affine.equation_neg ..).mpr h) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change affineEvaluation W x y h (affineNegationEquiv W (coord W false i)) =
    affineEvaluation W x ((W.map (algebraMap R S)).toAffine.negY x y)
      ((Affine.equation_neg ..).mpr h) (coord W false i)
  fin_cases i <;>
    simp [Affine.negY, WeierstrassCurve.map]

/-- The classical nonsingular point defines a morphism from the spectrum of its field. -/
def fieldPointMorphism {K : Type u} [Field K] [Algebra R K] :
    (W.map (algebraMap R K)).toAffine.Point → (Spec (.of K) ⟶ scheme W)
  | .zero => Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ infinity W
  | .some x y h =>
    Spec.map (CommRingCat.ofHom (affineEvaluation W x y h.1).toRingHom) ≫ affineChart W

@[reassoc (attr := simp)] theorem fieldPointMorphism_toBase
    {K : Type u} [Field K] [Algebra R K]
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointMorphism W P ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  cases P with
  | zero => simp [fieldPointMorphism]
  | some x y h =>
    simp only [fieldPointMorphism, Category.assoc, affineChart_toBase, chartToBase]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (affineEvaluation W x y h.1).comp_algebraMap

@[reassoc] theorem fieldPointMorphism_neg
    {K : Type u} [Field K] [Algebra R K]
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointMorphism W (-P) = fieldPointMorphism W P ≫ negation W := by
  cases P with
  | zero => simp only [← Affine.Point.zero_def]; simp [fieldPointMorphism]
  | some x y h =>
    simp only [Affine.Point.neg_some, fieldPointMorphism, Category.assoc, affineChart_negation]
    unfold affineNegation
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact (congrArg AlgHom.toRingHom (affineEvaluation_neg W x y h.1)).symm

/-- Two classical points, viewed as one point of the cubic product. -/
def fieldPointPair {K : Type u} [Field K] [Algebra R K]
    (P Q : (W.map (algebraMap R K)).toAffine.Point) :
    Spec (.of K) ⟶ pullback (toBase W) (toBase W) :=
  pullback.lift (fieldPointMorphism W P) (fieldPointMorphism W Q) (by simp)

@[reassoc (attr := simp)] theorem fieldPointPair_fst
    {K : Type u} [Field K] [Algebra R K]
    (P Q : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointPair W P Q ≫ pullback.fst (toBase W) (toBase W) = fieldPointMorphism W P :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem fieldPointPair_snd
    {K : Type u} [Field K] [Algebra R K]
    (P Q : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointPair W P Q ≫ pullback.snd (toBase W) (toBase W) = fieldPointMorphism W Q :=
  pullback.lift_snd _ _ _

theorem fieldPointPair_zero_left
    {K : Type u} [Field K] [Algebra R K]
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointPair W 0 P = fieldPointMorphism W P ≫ leftIdentityPair W := by
  apply pullback.hom_ext <;> simp [leftIdentityPair]
  rfl

theorem fieldPointPair_zero_right
    {K : Type u} [Field K] [Algebra R K]
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointPair W P 0 = fieldPointMorphism W P ≫ rightIdentityPair W := by
  apply pullback.hom_ext <;> simp [rightIdentityPair]
  rfl

theorem fieldPointPair_inverse
    {K : Type u} [Field K] [Algebra R K]
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointPair W P (-P) = fieldPointMorphism W P ≫ inverseGraph W := by
  apply pullback.hom_ext <;> simp [fieldPointPair, inverseGraph, fieldPointMorphism_neg]

theorem fieldPointPair_some
    {K : Type u} [Field K] [Algebra R K] {x y z t : K}
    (hP : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (hQ : (W.map (algebraMap R K)).toAffine.Nonsingular z t) :
    fieldPointPair W (.some x y hP) (.some z t hQ) =
      chartPairEvaluation W false false
        (affineEvaluation W x y hP.1) (affineEvaluation W z t hQ.1) := by
  apply pullback.hom_ext <;> simp [fieldPointPair, fieldPointMorphism, sourceChart]

end WeierstrassCurve.CubicCharts
