/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchExt

/-!
# Full branch tests for closed factorization through an arithmetic node

The two punctured branches detect ideal containment for the entire node.
The regular sum coordinate retains nilpotents, so no reduced-image argument
is needed when constructing a map into a closed subscheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (t : R)
  [TopologicalSpace.NoetherianSpace (chart R t)]

/-- The two full punctures detect containment in the kernel of an original node map. -/
theorem le_kernel_of_branches {Y : Scheme} (f : chart R t ⟶ Y)
    (I : Y.IdealSheafData)
    (hl : I ≤ (leftBranchOpen R t ≫ f).ker)
    (hr : I ≤ (rightBranchOpen R t ≫ f).ker) : I ≤ f.ker := by
  let U : Bool → (chart R t).Opens := fun b ↦
    if b then (rightBranchOpen R t).opensRange else (leftBranchOpen R t).opensRange
  let V := ⨆ b, U b
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
  have hV : V.ι.ker = ⊥ := by
    apply le_bot_iff.mp
    calc
      V.ι.ker ≤ (IsOpenImmersion.lift V.ι d hd ≫ V.ι).ker :=
        Scheme.Hom.le_ker_comp _ _
      _ = d.ker := by rw [IsOpenImmersion.lift_fac]
      _ = ⊥ := (branchSum_schematicallyDense t).ker_eq_bot
  let _ : TopologicalSpace.NoetherianSpace V.toScheme :=
    TopologicalSpace.NoetherianSpace.set (V : Set (chart R t))
  let _ : QuasiCompact (V.ι ≫ f) := quasiCompact_of_noetherianSpace_source _
  have he : I ≤ (V.ι ≫ f).ker := by
    rw [← Scheme.Hom.iInf_ker_openCover_map_comp _ (Scheme.Opens.iSupOpenCover U)]
    apply le_iInf
    intro b
    change Bool at b
    change I ≤ ((chart R t).homOfLE (le_iSup U b) ≫ (V.ι ≫ f)).ker
    rw [← Category.assoc, Scheme.homOfLE_ι]
    cases b
    · change I ≤ ((leftBranchOpen R t).opensRange.ι ≫ f).ker
      rw [← Scheme.Hom.ker_comp_of_isIso (leftBranchOpen R t).isoOpensRange.hom]
      simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc] using hl
    · change I ≤ ((rightBranchOpen R t).opensRange.ι ≫ f).ker
      rw [← Scheme.Hom.ker_comp_of_isIso (rightBranchOpen R t).isoOpensRange.hom]
      simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc] using hr
  rwa [Scheme.Hom.ker_comp, hV, Scheme.IdealSheafData.map_bot] at he

end FLT.Mazur.PolygonSmoothing
