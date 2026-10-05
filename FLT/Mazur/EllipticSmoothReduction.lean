/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticProjectiveReduction

/-!
# The nonsingular-reduction locus

Define the actual nonsingular-reduction locus and the fiber above infinity for
an integral Weierstrass equation. Both contain zero and are stable under negation.
The map on the nonsingular locus takes values in the smooth special-fiber group.
Additive closure and additivity of this map are separate obligations; no subgroup
or reduction homomorphism is asserted here.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Projective negation preserves primitive integral coordinates. -/
theorem unitCoordinate_neg {v : Fin 3 → A} (hv : UnitCoordinate A v) :
    UnitCoordinate A (W.toProjective.neg v) := by
  classical
  by_contra hn
  have hz (i) : residue A (W.toProjective.neg v i) = 0 := by
    by_contra hi
    exact hn ⟨i, (residue_ne_zero_iff_isUnit _).mp hi⟩
  have hx : residue A (v 0) = 0 := hz 0
  have hzz : residue A (v 2) = 0 := hz 2
  have hy := hz 1
  change residue A (-v 1 - W.a₁ * v 0 - W.a₃ * v 2) = 0 at hy
  simp only [map_sub, map_neg, map_mul, hx, hzz, mul_zero, sub_zero, neg_eq_zero] at hy
  obtain ⟨i, hi⟩ := hv
  have hi' := (residue_ne_zero_iff_isUnit (v i)).mpr hi
  fin_cases i
  · exact hi' hx
  · exact hi' hy
  · exact hi' hzz

/-- Negate a primitive representative of an actual generic point. -/
def PrimitiveLift.neg {P : (W.map (algebraMap A K)).toProjective.Point}
    (v : PrimitiveLift A P.point) : PrimitiveLift A (-P).point where
  coords := W.toProjective.neg v.coords
  primitive := unitCoordinate_neg A W v.primitive
  represents := by
    rw [Point.neg_point]
    conv_rhs => rw [← v.represents, negMap_eq]
    exact congrArg Quotient.mk'' (Projective.map_neg (algebraMap A K) v.coords).symm

/-- Projective reduction commutes with negation, including singular reductions. -/
theorem projectiveReduction_neg (P : (W.map (algebraMap A K)).toProjective.Point) :
    projectiveReduction A W (-P) =
      (W.map (residue A)).toProjective.negMap (projectiveReduction A W P) := by
  rw [projectiveReduction_eq A W (-P) ((primitiveLift A W P).neg A W)]
  change (⟦residue A ∘ W.toProjective.neg (primitiveLift A W P).coords⟧ :
    PointClass (ResidueField A)) =
      (W.map (residue A)).toProjective.negMap ⟦residue A ∘ (primitiveLift A W P).coords⟧
  rw [negMap_eq, Projective.map_neg]

/-- The locus of generic points with nonsingular projective reduction. -/
def SmoothReduction (P : (W.map (algebraMap A K)).toProjective.Point) : Prop :=
  (W.map (residue A)).toProjective.NonsingularLift (projectiveReduction A W P)

/-- The projective reduction fiber above infinity. -/
def InfinityReduction (P : (W.map (algebraMap A K)).toProjective.Point) : Prop :=
  projectiveReduction A W P = ⟦![0, 1, 0]⟧

/-- The infinity fiber lies in the nonsingular-reduction locus. -/
theorem InfinityReduction.smooth {P : (W.map (algebraMap A K)).toProjective.Point}
    (h : InfinityReduction A W P) : SmoothReduction A W P := by
  change (W.map (residue A)).toProjective.NonsingularLift _
  rw [show projectiveReduction A W P = ⟦![0, 1, 0]⟧ from h]
  exact nonsingularLift_zero

/-- Zero lies in the infinity fiber. -/
@[simp] theorem infinityReduction_zero : InfinityReduction A W 0 :=
  projectiveReduction_zero A W

/-- Zero lies in the nonsingular-reduction locus. -/
@[simp] theorem smoothReduction_zero : SmoothReduction A W 0 :=
  (infinityReduction_zero A W).smooth A W

/-- Nonsingular reduction is preserved by negation. -/
theorem SmoothReduction.neg {P : (W.map (algebraMap A K)).toProjective.Point}
    (h : SmoothReduction A W P) : SmoothReduction A W (-P) := by
  unfold SmoothReduction at *
  rw [projectiveReduction_neg]
  exact nonsingularLift_negMap h

/-- The infinity fiber is preserved by negation. -/
theorem InfinityReduction.neg {P : (W.map (algebraMap A K)).toProjective.Point}
    (h : InfinityReduction A W P) : InfinityReduction A W (-P) := by
  unfold InfinityReduction at *
  rw [projectiveReduction_neg, h]
  exact negMap_of_Z_eq_zero nonsingular_zero rfl

/-- Reduction on the nonsingular locus, valued in actual smooth special-fiber points. -/
noncomputable def smoothReductionPoint
    (P : {P : (W.map (algebraMap A K)).toProjective.Point // SmoothReduction A W P}) :
    (W.map (residue A)).toProjective.Point := ⟨P.property⟩

/-- The fiber above the identity is exactly the infinity-reduction condition. -/
theorem smoothReductionPoint_eq_zero_iff
    (P : {P : (W.map (algebraMap A K)).toProjective.Point // SmoothReduction A W P}) :
    smoothReductionPoint A W P = 0 ↔ InfinityReduction A W P.val :=
  Point.ext_iff

/-- Integral affine points belong to the locus exactly when their reduced coordinates are smooth. -/
theorem smoothReduction_affine_iff (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K)) :
    SmoothReduction A W (Affine.Point.toProjective (.some _ _ h)) ↔
      (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) := by
  unfold SmoothReduction
  rw [projectiveReduction_affine]
  exact nonsingularLift_some _ _

/-- An integral affine point never belongs to the infinity fiber. -/
theorem not_infinityReduction_affine (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K)) :
    ¬ InfinityReduction A W (Affine.Point.toProjective (.some _ _ h)) := by
  unfold InfinityReduction
  rw [projectiveReduction_affine]
  exact fun he => not_equiv_of_Z_eq_zero_left (P := ![0, 1, 0])
    (Q := ![residue A x, residue A y, 1]) rfl one_ne_zero (Quotient.exact he.symm)

end FLT.Mazur
