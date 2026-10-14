/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingSumRegular
public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Full arithmetic node maps are detected on the two punctured branches

The two Laurent branches contain the schematically dense principal open
D(x+y). Equality on both branches therefore determines maps from the whole
node chart to a separated target, even over a nonreduced base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)

/-- Both full punctured branches detect morphisms from the original arithmetic node. -/
theorem branch_hom_ext {Y S : Scheme} (s : Y ⟶ S) [IsSeparated s]
    (f g : chart R t ⟶ Y) (hb : f ≫ s = g ≫ s)
    (hl : leftBranchOpen R t ≫ f = leftBranchOpen R t ≫ g)
    (hr : rightBranchOpen R t ≫ f = rightBranchOpen R t ≫ g) : f = g := by
  let U : Bool → (chart R t).Opens := fun b ↦
    if b then (rightBranchOpen R t).opensRange else (leftBranchOpen R t).opensRange
  let V := ⨆ b, U b
  have he : V.ι ≫ f = V.ι ≫ g := by
    apply (Scheme.Opens.iSupOpenCover U).hom_ext
    intro b
    change Bool at b
    change (chart R t).homOfLE (le_iSup U b) ≫ (V.ι ≫ f) =
      (chart R t).homOfLE (le_iSup U b) ≫ (V.ι ≫ g)
    rw [← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι]
    cases b
    · change (leftBranchOpen R t).opensRange.ι ≫ f =
        (leftBranchOpen R t).opensRange.ι ≫ g
      rw [← cancel_epi (leftBranchOpen R t).isoOpensRange.hom]
      simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc] using hl
    · change (rightBranchOpen R t).opensRange.ι ≫ f =
        (rightBranchOpen R t).opensRange.ι ≫ g
      rw [← cancel_epi (rightBranchOpen R t).isoOpensRange.hom]
      simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc] using hr
  let d := PrincipalAffineRefinement.inclusion (leftCoordinate t + rightCoordinate t)
  have hd : Set.range d ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    rw [PrincipalAffineRefinement.range_inclusion] at hx
    change leftCoordinate t + rightCoordinate t ∉ x.asIdeal at hx
    apply TopologicalSpace.Opens.mem_iSup.mpr
    by_cases hlx : leftCoordinate t ∈ x.asIdeal
    · refine ⟨true, ?_⟩
      change x ∈ Set.range (rightBranchOpen R t)
      rw [rightBranchOpen_range]
      exact fun hrx ↦ hx (x.asIdeal.add_mem hlx hrx)
    · refine ⟨false, ?_⟩
      change x ∈ Set.range (leftBranchOpen R t)
      rwa [leftBranchOpen_range]
  apply branchSum_hom_ext t s f g hb
  calc
    d ≫ f = IsOpenImmersion.lift V.ι d hd ≫ V.ι ≫ f :=
      (IsOpenImmersion.lift_fac_assoc _ _ _ _).symm
    _ = IsOpenImmersion.lift V.ι d hd ≫ V.ι ≫ g := congrArg (_ ≫ ·) he
    _ = d ≫ g := IsOpenImmersion.lift_fac_assoc _ _ _ _

end FLT.Mazur.PolygonSmoothing
