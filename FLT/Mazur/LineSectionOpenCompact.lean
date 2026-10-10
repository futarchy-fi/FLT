/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineLineCover

/-!
# Compact generator opens of line sections

On a finite affine trivializing cover, a section's nonvanishing locus is a
finite union of principal affine opens. Thus it is compact even when the
ambient scheme is not Noetherian.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

namespace FLT.Mazur.FCurve

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- Inside an affine trivializing chart, the generator open is affine. -/
theorem isAffineOpen_inf_sectionGeneratorOpen (hL : LocallyFreeRankOne L)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e : L.restrict U.ι ≅ structureModule U.toScheme) (s : Γ(L, ⊤)) :
    IsAffineOpen (U ⊓ sectionGeneratorOpen L s) := by
  let t : Γ(L.restrict U.ι, ⊤) := L.presheaf.map (homOfLE le_top).op s
  have he : U.ι ⁻¹ᵁ sectionGeneratorOpen L s =
      U.toScheme.basicOpen (e.hom.app ⊤ t) := by
    rw [← sectionGeneratorOpen_restrict hL U.ι s,
      ← sectionGeneratorOpen_iso e, sectionGeneratorOpen_structure]
    rfl
  let _ : IsAffine U.toScheme := hU
  have ha : IsAffineOpen (U.ι ⁻¹ᵁ sectionGeneratorOpen L s) := by
    rw [he]
    exact (isAffineOpen_top U.toScheme).basicOpen _
  simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using ha.image_of_isOpenImmersion U.ι

/-- Generator opens of line sections are compact on every compact scheme. -/
theorem LocallyFreeRankOne.isCompact_sectionGeneratorOpen [CompactSpace X]
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) :
    IsCompact (sectionGeneratorOpen L s : Set X) := by
  obtain ⟨ι, hι, U, hU, e, hcover⟩ := hL.finite_affine_trivializing_cover
  let _ := hι
  have ha (i : ι) : IsAffineOpen (U i ⊓ sectionGeneratorOpen L s) :=
    isAffineOpen_inf_sectionGeneratorOpen hL (U i) (hU i) (e i).some s
  have he : (⨆ i, U i ⊓ sectionGeneratorOpen L s) = sectionGeneratorOpen L s := by
    rw [← iSup_inf_eq, hcover, top_inf_eq]
  rw [← he, Opens.coe_iSup]
  exact isCompact_iUnion (fun i ↦ (ha i).isCompact)

end FLT.Mazur.FCurve
