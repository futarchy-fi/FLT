/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicIntegerFunctionRelation

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
local notation "V" => integerSourceOpen n b
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The full relation restricts to the original characteristic source open. -/
theorem integerSourceOpen_preimage_eq : src ⁻¹ᵁ V = tgt ⁻¹ᵁ V :=
  pullOpen_preimage_eq n (integerOpen n (chartInteger (!b)))

/-- The assembled function is invariant in the original ambient open-section coordinates. -/
theorem integerSourceFunction_mem (s : chartResidualSections n (!b)) :
    (V).topIso.hom (integerSourceFunction n b s) ∈
      originalInvariantSections n V (integerSourceOpen_preimage_eq n b) := by
  have he := integerSourceFunction_relation n b s
    ((src).resLE V (src ⁻¹ᵁ V) le_rfl)
    ((tgt).resLE V (src ⁻¹ᵁ V) (integerSourceOpen_preimage_eq n b).le)
    (src ⁻¹ᵁ V).ι
    ((src).resLE_comp_ι le_rfl).symm
    ((tgt).resLE_comp_ι (integerSourceOpen_preimage_eq n b).le).symm
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    CommRingCat.comp_apply] at he
  have he' := (src ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.injective he
  change (src).app V ((V).topIso.hom (integerSourceFunction n b s)) =
    (tgt).appLE V (src ⁻¹ᵁ V) (integerSourceOpen_preimage_eq n b).le
      ((V).topIso.hom (integerSourceFunction n b s))
  simpa only [Scheme.Hom.appLE_eq_app] using he'

/-- The full residual invariant gives an original invariant section on the source domain. -/
def integerSourceOriginalInvariantHom : chartResidualSections n (!b) →+*
    originalInvariantSections n V (integerSourceOpen_preimage_eq n b) :=
  ((V).topIso.hom.hom.comp (integerSourceFunctionHom n b)).codRestrict _
    (integerSourceFunction_mem n b)

/-- Reconstruct an actual invariant-sheaf section from the full residual invariant. -/
def integerInvariantReconstruction : chartResidualSections n (!b) →+*
    (invariantSheaf n).obj.obj (op (integerOpen n (chartInteger (!b)))) :=
  (invariantSectionRingEquivOn n (integerOpen n (chartInteger (!b))) V rfl
    (integerSourceOpen_preimage_eq n b)).symm.toRingHom.comp
      (integerSourceOriginalInvariantHom n b)

/-- The reconstructed invariant section has exactly the assembled original source value. -/
theorem integerInvariantReconstruction_inclusion (s : chartResidualSections n (!b)) :
    (invariantInclusion n).hom.app (op (integerOpen n (chartInteger (!b))))
        (integerInvariantReconstruction n b s) =
      (V).topIso.hom (integerSourceFunction n b s) := by
  have h := (invariantSectionRingEquivOn n (integerOpen n (chartInteger (!b))) V rfl
    (integerSourceOpen_preimage_eq n b)).apply_symm_apply
      (integerSourceOriginalInvariantHom n b s)
  have he := congrArg Subtype.val h
  rw [invariantSectionRingEquivOn_val] at he
  rw [eqToHom_refl, (normalizedDisjointSource n).presheaf.map_id] at he
  exact he

end FLT.Mazur.CyclicCharacteristicOrbit
