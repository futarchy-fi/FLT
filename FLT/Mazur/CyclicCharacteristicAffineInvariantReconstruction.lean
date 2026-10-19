/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineFunctionRelation

/-!
# Reconstructing actual invariant-sheaf sections

The assembled function satisfies the full relation on the original source
open. Explicit top-section transport then places it in the original invariant
subring and hence in the section ring of the actual quotient sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀)
local notation "V" => affineSourceOpen n b j
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The full relation restricts to the original characteristic source open. -/
theorem affineSourceOpen_preimage_eq : src ⁻¹ᵁ V = tgt ⁻¹ᵁ V :=
  pullOpen_preimage_eq n (affineOrbitOpen n ⟨!b, j⟩)

/-- The assembled function is invariant in the original ambient open-section coordinates. -/
theorem affineSourceFunction_mem (s : affineResidualSections n ⟨!b, j⟩) :
    (V).topIso.hom (affineSourceFunction n b j s) ∈
      originalInvariantSections n V (affineSourceOpen_preimage_eq n b j) := by
  have he := affineSourceFunction_relation n b j s
    ((src).resLE V (src ⁻¹ᵁ V) le_rfl)
    ((tgt).resLE V (src ⁻¹ᵁ V) (affineSourceOpen_preimage_eq n b j).le)
    (src ⁻¹ᵁ V).ι
    ((src).resLE_comp_ι le_rfl).symm
    ((tgt).resLE_comp_ι (affineSourceOpen_preimage_eq n b j).le).symm
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    CommRingCat.comp_apply] at he
  have he' := (src ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.injective he
  change (src).app V ((V).topIso.hom (affineSourceFunction n b j s)) =
    (tgt).appLE V (src ⁻¹ᵁ V) (affineSourceOpen_preimage_eq n b j).le
      ((V).topIso.hom (affineSourceFunction n b j s))
  simpa only [Scheme.Hom.appLE_eq_app] using he'

/-- The full residual invariant gives an original invariant section on the source domain. -/
def affineSourceOriginalInvariantHom : affineResidualSections n ⟨!b, j⟩ →+*
    originalInvariantSections n V (affineSourceOpen_preimage_eq n b j) :=
  ((V).topIso.hom.hom.comp (affineSourceFunctionHom n b j)).codRestrict _
    (affineSourceFunction_mem n b j)

/-- Reconstruct an actual invariant-sheaf section from the full residual invariant. -/
def affineInvariantReconstruction : affineResidualSections n ⟨!b, j⟩ →+*
    (invariantSheaf n).obj.obj (op (affineOrbitOpen n ⟨!b, j⟩)) :=
  (invariantSectionRingEquivOn n (affineOrbitOpen n ⟨!b, j⟩) V rfl
    (affineSourceOpen_preimage_eq n b j)).symm.toRingHom.comp
      (affineSourceOriginalInvariantHom n b j)

/-- The reconstructed invariant section has exactly the assembled original source value. -/
theorem affineInvariantReconstruction_inclusion (s : affineResidualSections n ⟨!b, j⟩) :
    (invariantInclusion n).hom.app (op (affineOrbitOpen n ⟨!b, j⟩))
        (affineInvariantReconstruction n b j s) =
      (V).topIso.hom (affineSourceFunction n b j s) := by
  have h := (invariantSectionRingEquivOn n (affineOrbitOpen n ⟨!b, j⟩) V rfl
    (affineSourceOpen_preimage_eq n b j)).apply_symm_apply
      (affineSourceOriginalInvariantHom n b j s)
  have he := congrArg Subtype.val h
  rw [invariantSectionRingEquivOn_val] at he
  rw [eqToHom_refl, (normalizedDisjointSource n).presheaf.map_id] at he
  exact he

end FLT.Mazur.CyclicCharacteristicOrbit
