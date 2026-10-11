/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierComplementRestriction
public import FLT.Mazur.DivisorInvertibleSheaf

/-!
# Cartier complements detect line-bundle sections

Local trivializations reduce equality of line sections to faithful restriction
of regular functions. No irreducibility or reducedness is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- A line section vanishing off an effective Cartier divisor vanishes everywhere. -/
theorem LocallyFreeRankOne.cartierComplement_restrict_injective {M : X.Modules}
    (hM : LocallyFreeRankOne M) (hI : EffectiveCartier I) (W : X.Opens) :
    Function.Injective (M.presheaf.map
      (homOfLE (show W ⊓ I.support.compl ≤ W from inf_le_left)).op) := by
  intro s t he
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM x
  let A : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  let B : U.toScheme.Opens := A ⊓ (I.comap U.ι).support.compl
  have hAW : U.ι ''ᵁ A ≤ W := U.ι.image_preimage_le W
  have hxA : x ∈ U.ι ''ᵁ A := by
    exact ⟨⟨x, hxU⟩, hx, rfl⟩
  have hBA : B ≤ A := inf_le_left
  have hBC : B ≤ U.ι ⁻¹ᵁ I.support.compl := by
    intro z hz
    change U.ι z ∉ I.support
    have hz' : z ∉ (I.comap U.ι).support := hz.2
    rw [Scheme.IdealSheafData.support_comap] at hz'
    exact hz'
  have hBW : U.ι ''ᵁ B ≤ W ⊓ I.support.compl := by
    exact le_inf ((U.ι.image_mono hBA).trans hAW)
      ((U.ι.image_mono hBC).trans (U.ι.image_preimage_le _))
  refine ⟨U.ι ''ᵁ A, hAW, hxA, ?_⟩
  let sA := (M.restrictAppIso U.ι A).inv (M.presheaf.map (homOfLE hAW).op s)
  let tA := (M.restrictAppIso U.ι A).inv (M.presheaf.map (homOfLE hAW).op t)
  suffices h : sA = tA by exact h
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app A)).injective
  have hscalar : Function.Injective (U.toScheme.presheaf.map (homOfLE hBA).op) := by
    exact FLT.Mazur.FCurve.cartierComplement_restrict_injective
      (hI.comap_of_isOpenImmersion U.ι) A
  apply hscalar
  have hn := e.hom.mapPresheaf.naturality (homOfLE hBA).op
  have hh := congrArg (M.presheaf.map (homOfLE hBW).op) he
  have hab : (M.restrict U.ι).presheaf.map (homOfLE hBA).op sA =
      (M.restrict U.ι).presheaf.map (homOfLE hBA).op tA := by
    change M.presheaf.map (homOfLE (U.ι.image_mono hBA)).op
        (M.presheaf.map (homOfLE hAW).op s) =
      M.presheaf.map (homOfLE (U.ι.image_mono hBA)).op
        (M.presheaf.map (homOfLE hAW).op t)
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, homOfLE_comp] using hh
  exact (ConcreteCategory.congr_hom hn sA).symm.trans
    ((congrArg (e.hom.app B) hab).trans (ConcreteCategory.congr_hom hn tA))

end FLT.Mazur.FCurve
