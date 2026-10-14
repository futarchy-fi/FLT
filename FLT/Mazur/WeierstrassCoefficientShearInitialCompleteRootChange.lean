/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialLineRootChange
public import FLT.Mazur.WeierstrassCoefficientShearInitialCompleteNormalization
public import FLT.Mazur.ProjectiveLineCompanionSlopeTranslation

/-!
# Companion-root comparison of the complete independent exterior

The actual affine slope translation extends across infinity by separatedness.
Its signed ordered coordinates give the complete companion exterior reversal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r t : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
local notation "Nr" => coefficientShearInitialCompleteNormalization
  hπ data S r j hj hs h3 h4 hr
local notation "Nt" => coefficientShearInitialCompleteNormalization
  hπ data S t j hj hs h3 h4 ht
local notation "M" => coefficientShearRootChange hπ data S r t j hj
local notation "pt" => coefficientShearGluedStructure hπ data S t j hj
variable (a : Sˣ)
  (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
open ProjectiveLine
include ha hrt

omit [IsDomain R] [IsBezout R] in
/-- The actual root difference is the first root's signed tangent unit. -/
theorem coefficientShearInitialCompanion_difference : r - t = (a : S) := by
  rw [ha, (rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1]
  change r - t = algebraMap R S W.a₁ + 2 * r
  linear_combination -hrt

/-- The independently extended full exteriors differ by the actual companion slope translation. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_rootChange :
    Nr ≫ (M).hom = (companionSlopeTranslation a).hom ≫ Nt := by
  let _ : IsSeparated pt := by
    unfold coefficientShearGluedStructure
    infer_instance
  refine ext_of_isDominant_of_isSeparated pt ?_ (left S) ?_
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearInitialCompleteNormalization_structure, Category.assoc,
      coefficientShearInitialCompleteNormalization_structure, companionSlopeTranslation_base]
  · rw [coefficientShearInitialCompleteNormalization_left_assoc,
      companionSlopeTranslation_left_assoc,
      coefficientShearInitialCompleteNormalization_left,
      coefficientShearRootChange_initialLine]
    rw [coefficientShearInitialCompanion_difference S r t a ha hrt]

/-- Opposite ordered coordinates are the independent full companion-root normalization. -/
@[reassoc] theorem coefficientShearInitialCompleteNormalization_opposite :
    endpointReversal S ≫ (slopeNormalizationIso a).inv ≫ Nr ≫ (M).hom =
      (slopeNormalizationIso (-a)).inv ≫ Nt := by
  rw [coefficientShearInitialCompleteNormalization_rootChange
    hπ data S r t j hj hs h3 h4 hr ht a ha hrt]
  have H : endpointReversal S ≫ (slopeNormalizationIso a).inv ≫
      (companionSlopeTranslation a).hom = (slopeNormalizationIso (-a)).inv := by
    apply (cancel_mono (slopeNormalizationIso (-a)).hom).mp
    rw [Category.assoc, Category.assoc, companionSlopeTranslation_normalization,
      Iso.inv_hom_id_assoc, endpointReversal_involutive, Iso.inv_hom_id]
  simpa only [Category.assoc] using congrArg (· ≫ Nt) H

end FLT.Mazur.WeierstrassDividedDepth
