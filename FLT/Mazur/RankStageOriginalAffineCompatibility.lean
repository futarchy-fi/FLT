/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAffineRepresentatives

/-!
# Rank-core compatibility gives original adic differences

Compatible full core coefficients, represented on the fixed original affine
neighborhood, differ by the exact lower rank ideal power. This identifies
an actual adic sequence in the original ring, without completing that ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance affineCompatOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineCompatOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineCompatOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha


local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
local notation "j" => rankStageTransition (Over.mk p) n
local notation "V" k => (I ^ (k + 1)).subschemeι ⁻¹ᵁ U.1

/-- Core compatibility is equality of actual sections on the open in the lower stage. -/
theorem rankStageCoreRestriction_section {k l : ℕ} (h : k ≤ l)
    (v : rankStageCoreInvariants e n a ha l) :
    (j h).appLE (C l) (C k) (rankStageCore_preimage e n a ha h).ge
        ((C l).topIso.hom v.val) =
      (C k).topIso.hom (rankStageCoreRestriction e n a ha h v).val := by
  rw [rankStageCoreRestriction_val]
  change _ = (C k).topIso.hom
    (((j h).resLE (C l) (C k) (rankStageCore_preimage e n a ha h).ge).app ⊤ v.val)
  rw [Scheme.Hom.resLE_app_top]
  exact ((C k).topIso.commRingCatIsoToRingEquiv.apply_symm_apply _).symm

/-- Restricting the compatible core sequence keeps its exact order-transition equation. -/
theorem rankStageCoreAffineCoefficient_compatible {k l : ℕ} (h : k ≤ l)
    (hk : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k)
    (hl : rankThickeningMap (Over.mk p) n l ⁻¹ᵁ A.basicOpen b ≤ C l)
    (v : rankStageCoreInvariants e n a ha l) :
    (j h).appLE (V l) (V k) (by
        change _ ≤ (j h ≫ (I ^ (l + 1)).subschemeι) ⁻¹ᵁ U.1
        rw [rankStageTransition, Scheme.IdealSheafData.inclusion_subschemeι])
        (rankStageCoreAffineCoefficient e n a ha b hb l hl v.val) =
      rankStageCoreAffineCoefficient e n a ha b hb k hk
        (rankStageCoreRestriction e n a ha h v).val := by
  unfold rankStageCoreAffineCoefficient
  rw [← rankStageCoreRestriction_section]
  have hv : (V k) ≤ j h ⁻¹ᵁ (V l) := by
    change _ ≤ (j h ≫ (I ^ (l + 1)).subschemeι) ⁻¹ᵁ U.1
    rw [rankStageTransition, Scheme.IdealSheafData.inclusion_subschemeι]
  have he : (rankThickening (Over.mk p) n l).presheaf.map (homOfLE hl).op ≫
      (j h).appLE (V l) (V k) hv =
      (j h).appLE (C l) (C k) (rankStageCore_preimage e n a ha h).ge ≫
        (rankThickening (Over.mk p) n k).presheaf.map (homOfLE hk).op := by
    exact ((j h).map_appLE hv (homOfLE hl).op).trans
      ((j h).appLE_map (rankStageCore_preimage e n a ha h).ge (homOfLE hk).op).symm
  exact congrArg (fun r ↦ r ((C l).topIso.hom v.val)) he

/-- Any original representatives of compatible core values have the exact adic difference. -/
theorem rankStage_original_affine_difference {k l : ℕ} (h : k ≤ l)
    (hk : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k)
    (hl : rankThickeningMap (Over.mk p) n l ⁻¹ᵁ A.basicOpen b ≤ C l)
    (v : rankStageCoreInvariants e n a ha l) (w z : Γ(X, U.1))
    (hw : (I ^ (l + 1)).subschemeι.app U.1 w =
      rankStageCoreAffineCoefficient e n a ha b hb l hl v.val)
    (hz : (I ^ (k + 1)).subschemeι.app U.1 z =
      rankStageCoreAffineCoefficient e n a ha b hb k hk
        (rankStageCoreRestriction e n a ha h v).val) :
    w - z ∈ ((I).ideal U) ^ (k + 1) := by
  apply (rankStage_original_affine_same_image_iff n b hb k w z).mp
  rw [hz, ← rankStageCoreAffineCoefficient_compatible e n a ha b hb h hk hl, ← hw]
  have hv : (V k) ≤ j h ⁻¹ᵁ (V l) := by
    change _ ≤ (j h ≫ (I ^ (l + 1)).subschemeι) ⁻¹ᵁ U.1
    rw [rankStageTransition, Scheme.IdealSheafData.inclusion_subschemeι]
  have he : (I ^ (k + 1)).subschemeι.app U.1 =
      (I ^ (l + 1)).subschemeι.app U.1 ≫ (j h).appLE (V l) (V k) hv := by
    rw [← Scheme.Hom.comp_appLE]
    simp only [rankStageTransition, Scheme.IdealSheafData.inclusion_subschemeι]
    rw [← Scheme.Hom.app_eq_appLE]
  exact congrArg (fun r ↦ r w) he

end FLT.Mazur.EquivalenceRelationOrderedFrames
