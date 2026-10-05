/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerGeneratorOpen

/-!
# Affine generator opens inside a trivializing affine chart

On a trivial line, a section's generator open is an ordinary principal open.
A global generator open contained in an affine trivializing chart is therefore
affine in the ambient scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme} {L : X.Modules}

/-- Every point has an affine neighborhood trivializing its line sheaf. -/
theorem LocallyFreeRankOne.exists_affine_trivialization (hL : LocallyFreeRankOne L) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (L.restrict U.ι ≅ structureModule U.toScheme) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hL x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  refine ⟨U, hxU, hU, ⟨?_⟩⟩
  exact (restrictFunctorCongr (X.homOfLE_ι hUV).symm).app L ≪≫
    (restrictFunctorComp (X.homOfLE hUV) V.ι).app L ≪≫
    (restrictFunctor (X.homOfLE hUV)).mapIso e ≪≫ restrictUnitIso (X.homOfLE hUV)

/-- A global section whose generator open lies in an affine trivializing chart has affine open. -/
theorem isAffineOpen_sectionGeneratorOpen_of_le (hL : LocallyFreeRankOne L)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e : L.restrict U.ι ≅ structureModule U.toScheme)
    (s : Γ(L, ⊤)) (hs : sectionGeneratorOpen L s ≤ U) :
    IsAffineOpen (sectionGeneratorOpen L s) := by
  let t : Γ(L.restrict U.ι, ⊤) := L.presheaf.map (homOfLE le_top).op s
  have he : U.ι ⁻¹ᵁ sectionGeneratorOpen L s =
      U.toScheme.basicOpen (e.hom.app ⊤ t) := by
    rw [← sectionGeneratorOpen_restrict hL U.ι s,
      ← sectionGeneratorOpen_iso e, sectionGeneratorOpen_structure]
    rfl
  have : IsAffine U.toScheme := hU
  have ha : IsAffineOpen (U.ι ⁻¹ᵁ sectionGeneratorOpen L s) := by
    rw [he]
    exact (isAffineOpen_top U.toScheme).basicOpen _
  have him := ha.image_of_isOpenImmersion U.ι
  have hu : U.ι ''ᵁ (U.ι ⁻¹ᵁ sectionGeneratorOpen L s) = sectionGeneratorOpen L s := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hs]
  rwa [hu] at him

end FLT.Mazur.FCurve
