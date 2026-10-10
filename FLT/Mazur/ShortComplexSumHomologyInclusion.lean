/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologySumHomology

/-!
# Original inclusions in direct-sum homology

The finite-support cycles and quotient maps retain the component inclusion.
Consequently the existing homology comparison preserves each original summand.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped DirectSum

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

variable (R : Type u) [CommRing R] {κ : Type u} [DecidableEq κ]
  (T : κ → ShortComplex (ModuleCat.{u} R))

/-- The original inclusion of one short complex into the finite-support sum. -/
def shortSumInclusion (e : κ) : T e ⟶ exponentShortSum R T where
  τ₁ := ModuleCat.ofHom (DirectSum.lof R κ (fun k ↦ (T k).X₁) e)
  τ₂ := ModuleCat.ofHom (DirectSum.lof R κ (fun k ↦ (T k).X₂) e)
  τ₃ := ModuleCat.ofHom (DirectSum.lof R κ (fun k ↦ (T k).X₃) e)
  comm₁₂ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DirectSum.lmap_lof (fun k ↦ (T k).f.hom) e x
  comm₂₃ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DirectSum.lmap_lof (fun k ↦ (T k).g.hom) e x

/-- Both cycles and their quotient use the same original degree inclusion. -/
def shortSumInclusionHomologyData (e : κ) :
    ShortComplex.LeftHomologyMapData (shortSumInclusion R T e)
      (T e).moduleCatLeftHomologyData (sumLeftHomologyData R T) where
  φK := ModuleCat.ofHom (DirectSum.lof R κ (fun k ↦ LinearMap.ker (T k).g.hom) e)
  φH := ModuleCat.ofHom
    (DirectSum.lof R κ (fun k ↦ (T k).moduleCatLeftHomologyData.H) e)
  commi := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DirectSum.lmap_lof (fun k ↦ (LinearMap.ker (T k).g.hom).subtype) e x
  commf' := by
    change _ = _ ≫ (sumCyclesKernel R T).lift _
    rw [sumCyclesKernel_lift]
    apply ConcreteCategory.hom_ext
    intro x
    exact (DirectSum.lmap_lof (fun k ↦ (T k).moduleCatToCycles) e x).symm
  commπ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (DirectSum.lmap_lof
      (fun k ↦ (LinearMap.range (T k).moduleCatToCycles).mkQ) e x).symm

/-- The already constructed homology isomorphism preserves the actual inclusion. -/
lemma shortSumHomologyIso_inclusion (e : κ) (x : (T e).homology) :
    (shortSumHomologyIso R T).hom (ShortComplex.homologyMap (shortSumInclusion R T e) x) =
      DirectSum.of (fun k ↦ (T k).homology) e x := by
  have h := ConcreteCategory.congr_hom
    (shortSumInclusionHomologyData R T e).homologyMap_comm x
  simp only [ConcreteCategory.comp_apply] at h
  change (DFinsupp.mapRange.linearEquiv fun k ↦
    (T k).moduleCatHomologyIso.symm.toLinearEquiv)
      ((sumLeftHomologyData R T).homologyIso.hom
        (ShortComplex.homologyMap (shortSumInclusion R T e) x)) = _
  rw [h]
  change DirectSum.lmap (fun k ↦ (T k).moduleCatHomologyIso.inv.hom)
    (DirectSum.lof R κ (fun k ↦ (T k).moduleCatLeftHomologyData.H) e
      ((T e).moduleCatHomologyIso.hom x)) = _
  rw [DirectSum.lmap_lof]
  simp only [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  exact DirectSum.lof_eq_of R κ (fun k ↦ (T k).homology) e x

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
