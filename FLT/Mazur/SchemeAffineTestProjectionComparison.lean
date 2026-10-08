/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOpenProjectionComparison
public import FLT.Mazur.SchemeAffineTestProjectionRefinement

/-!
# Glued projection equations on arbitrary scheme tests

A test with coordinates in two open base charts factors through their
common image open. Refining the actual open projection equation gives the
ambient effective comparison on that test, without an affineness hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued openGluedProjection

/-- Glued projections recover the actual ambient comparison on every scheme test. -/
@[reassoc]
lemma openGluedProjection_schemeTest (i j : ι) (a : W ⟶ X)
    (b : W ⟶ Spec (C i).baseRing) (c : W ⟶ Spec (C j).baseRing)
    (hb : b ≫ (C i).base = a) (hc : c ≫ (C j).base = a) :
    (pullback a).map (openGluedProjection C D i) ≫
        (C i).ambientTestComparison (C j) D a b c hb hc =
      (pullback a).map (openGluedProjection C D j) := by
  let U := (C i).base.opensRange ⊓ (C j).base.opensRange
  have hr : Set.range a ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨w, rfl⟩
    exact ⟨⟨b w, congrArg (fun f : W ⟶ X ↦ f w) hb⟩,
      ⟨c w, congrArg (fun f : W ⟶ X ↦ f w) hc⟩⟩
  let t := IsOpenImmersion.lift U.ι a hr
  have ht : t ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hbi : t ≫ coordinate (C i).base U inf_le_left = b := by
    apply (cancel_mono (C i).base).mp
    rw [Category.assoc, coordinate_comp, ht, hb]
  have hcj : t ≫ coordinate (C j).base U inf_le_right = c := by
    apply (cancel_mono (C j).base).mp
    rw [Category.assoc, coordinate_comp, ht, hc]
  exact (C i).ambientProjection_refine (C j) D
    (openGluedProjection C D i) (openGluedProjection C D j) t U.ι a ht
    (coordinate (C i).base U inf_le_left) (coordinate (C j).base U inf_le_right)
    (coordinate_comp (C i).base U inf_le_left)
    (coordinate_comp (C j).base U inf_le_right) b c hbi hcj hb hc
    (openGluedProjection_openTest C D i j U inf_le_left inf_le_right)

end FLT.Mazur.SchemeAffineDescent
