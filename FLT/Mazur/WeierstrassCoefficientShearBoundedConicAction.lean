/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneConicAction

/-!
# Scale-one conic actions at an arbitrary bounded stage

Index by the total stage instead of an offset. Eliminating its lower bound
transports the entire action proposition, including its pullback compatibility.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (k : ℕ) (hjk : j + 1 ≤ k) (hkN : k ≤ n)
  (D : SplitNodeDepth W π depth) (hk0 : start + j = 0)
  (hk : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hk
    (Data.b6 d) (Data.factor6 d))
local notation "P₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicPuncturedFirst (W.map (residue R)) c hc)))
local notation "P₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicPuncturedSecond (W.map (residue R)) c hc)))
local notation "F" => zeroResidueConicImmersion D (start + j) hk0 (Nat.le_of_lt hk)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "B" => coefficientShearRetainedTensorChart hπ data K 0
  k hkN (Fin.mk j (by omega))
local notation "J" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalResidueConic D)))
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "u" => laurentUnitOverPoint (R := K) τ
local notation "g" => coefficientShearGluedStructure hπ data K 0 k hkN
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm K)
local notation "h" => splitDepth_zeroRoot_conditions D
local notation "A" => coefficientShearTorusAction hπ data K 0 k hkN a
  (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2

/-- The first complete conic puncture forms an actual torus-domain pair. -/
theorem coefficientShearScaleOneFirst_boundedCondition : (u).left ≫ t = (J ≫ P₁ ≫ F ≫ B) ≫ g := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact coefficientShearScaleOneFirst_condition hπ data j hj m hkN D hk0 hk

/-- The opposite complete conic puncture forms the other actual torus-domain pair. -/
theorem coefficientShearScaleOneSecond_boundedCondition : (u).left ≫ t = (J ≫ P₂ ≫ F ≫ B) ≫ g := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact coefficientShearScaleOneSecond_condition hπ data j hj m hkN D hk0 hk

/-- On the first actual scale-one conic puncture the full torus action multiplies by tau. -/
theorem coefficientShearTorusAction_scaleOneBoundedFirst :
    pullback.lift (u).left (J ≫ P₁ ≫ F ≫ B)
        (coefficientShearScaleOneFirst_boundedCondition hπ data j hj k hjk hkN D hk0 hk) ≫ A =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫
        P₁ ≫ F ≫ B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact coefficientShearTorusAction_scaleOneFirst hπ data j hj m hkN D hk0 hk

/-- On the opposite actual scale-one puncture the full action uses the inverse character. -/
theorem coefficientShearTorusAction_scaleOneBoundedSecond :
    pullback.lift (u).left (J ≫ P₂ ≫ F ≫ B)
        (coefficientShearScaleOneSecond_boundedCondition hπ data j hj k hjk hkN D hk0 hk) ≫ A =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫
        P₂ ≫ F ≫ B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact coefficientShearTorusAction_scaleOneSecond hπ data j hj m hkN D hk0 hk

end FLT.Mazur.WeierstrassDividedDepth
