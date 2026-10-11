/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalTensorAction
public import FLT.Mazur.WeierstrassSmoothHorizontalCyclicParameter
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialCharts
public import FLT.Mazur.ProjectiveLineUniversalLaurentEvaluation
public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals

/-!
# The constructed residue action in the original component-labeled finite model

The first conic parameter is the right coordinate of cyclic component one;
the opposite is the left coordinate of the final cyclic component. With the
proved cyclic unit tau inverse, both constructed action maps are restrictions
of universal projective scaling into these actual components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega) (Data.b6 d) (Data.factor6 d))
local notation "g" => globalInitialTensorChart hπ data 𝕂 (s + 1) hs
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc
local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z)))

/-- The actual first conic puncture is the right puncture of cyclic component one. -/
theorem initialConicFirstPuncture_cycle :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom P₁)) ≫
        initialGlobalConic hπ data D (s + 1) hs hstart (by omega) =
      ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.right 𝕂 ≫ (Z 1).left := by
  rw [conicPuncturedFirst_spec c hc (W.map (residue R)) (residue_tangent_isUnit D)]
  simp only [Category.assoc]
  change Spec.map _ ≫ initialGlobalConicFirstParameter hπ data D (s + 1) hs hstart _ = _
  rw [← conicZeroAffineIso_puncture c hc, Category.assoc,
    ← positiveEqualityCycleComponent_initial_first_chart hπ data D s hs hstart hk hp]

/-- The opposite puncture is the left puncture of the last cyclic component. -/
theorem initialConicSecondPuncture_cycle :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom P₂)) ≫
        initialGlobalConic hπ data D (s + 1) hs hstart (by omega) =
      ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.left 𝕂 ≫
        (Z ⟨2 * s + 3, by omega⟩).left := by
  rw [conicPuncturedSecond_spec c hc (W.map (residue R)) (residue_tangent_isUnit D)]
  simp only [Category.assoc]
  change Spec.map _ ≫ initialGlobalConicSecondParameter hπ data D (s + 1) hs hstart _ = _
  rw [← conicZeroAffineIso_puncture c hc, Category.assoc,
    ← positiveEqualityCycleComponent_initial_second_chart hπ data D s hs hstart hk hp]

/-- The first constructed action lands in the original finite model with its actual label. -/
theorem initialHorizontalFirstTensorAction_cycle :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalFirstTensorAction (k := start) D d hstart (by omega) hπ).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom
        (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫
          ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.right 𝕂 ≫ (Z 1).left := by
  rw [smoothHorizontalFirstTensorAction_conic, lineSpec_comp, lineSpec_comp, lineSpec_comp]
  simp only [Category.assoc]
  have h := initialConicFirstPuncture_cycle hπ data D s hs hstart hk hp
  exact congrArg (Spec.map (CommRingCat.ofHom
    (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫ ·) h

/-- The opposite constructed action retains the actual final cyclic component. -/
theorem initialHorizontalSecondTensorAction_cycle :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalSecondTensorAction (k := start) D d hstart (by omega) hπ).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom
        (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫
          ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.left 𝕂 ≫
            (Z ⟨2 * s + 3, by omega⟩).left := by
  rw [smoothHorizontalSecondTensorAction_conic, lineSpec_comp, lineSpec_comp, lineSpec_comp]
  simp only [Category.assoc]
  have h := initialConicSecondPuncture_cycle hπ data D s hs hstart hk hp
  exact congrArg (Spec.map (CommRingCat.ofHom
    (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫ ·) h

/-- The first constructed residue action is universal scaling on the actual component one. -/
theorem initialHorizontalFirstTensorAction_universal :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalFirstTensorAction (k := start) D d hstart (by omega) hπ).toRingHom) ≫ g =
      q ≫ ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true ≫
          ProjectiveLineUniversalAction.action 𝕂 ≫ (Z 1).left := by
  rw [initialHorizontalFirstTensorAction_cycle hπ data D s hs hstart hk hp]
  have h := congrArg (· ≫ (Z 1).left)
    (ProjectiveLineUniversalAction.laurentPairEvaluation_right_action (K := 𝕂) τ⁻¹ z)
  simp only [inv_inv, Category.assoc] at h
  exact h.symm

/-- The same cyclic parameter gives universal scaling on the opposite original component. -/
theorem initialHorizontalSecondTensorAction_universal :
    Spec.map (CommRingCat.ofHom
      (smoothHorizontalSecondTensorAction (k := start) D d hstart (by omega) hπ).toRingHom) ≫ g =
      q ≫ ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] false ≫
          ProjectiveLineUniversalAction.action 𝕂 ≫ (Z ⟨2 * s + 3, by omega⟩).left := by
  rw [initialHorizontalSecondTensorAction_cycle hπ data D s hs hstart hk hp]
  have h := congrArg (· ≫ (Z ⟨2 * s + 3, by omega⟩).left)
    (ProjectiveLineUniversalAction.laurentPairEvaluation_action (K := 𝕂) τ⁻¹ z)
  simp only [Category.assoc] at h
  exact h.symm

end FLT.Mazur.WeierstrassDividedDepth
