/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalEquation
public import FLT.Mazur.SchemeAffineOpenGluingProjection

/-!
# Projection comparisons on common base opens

The original transition equation restricts to every common subopen. It
therefore gives an equation between actual pullback projections, with the
independently constructed ambient test comparison in the middle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open ModuleSheafOpenImageChart ModuleSheafMorphismGluing
open ModuleSheafOpenImmersionLocalHom
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued openGluedProjection

/-- The actual glued projections obey the comparison on every smaller common open. -/
lemma openGluedProjection_openTest_eval (i j : ι) (U : X.Opens)
    (hi : U ≤ (C i).base.opensRange) (hj : U ≤ (C j).base.opensRange)
    (V : X.Opens) (hV : V ≤ U) (s : Γ(openGlued C D, V)) :
    localEval ((C i).openTestIso (C j) D U hi hj).hom hV
        ((openGluedProjection C D i).app V s) =
      (openGluedProjection C D j).app V s := by
  rw [(C i).openTestIso_refine_eval (C j) D
    ((C i).base.opensRange ⊓ (C j).base.opensRange) U
    inf_le_left inf_le_right (le_inf hi hj)]
  exact localEval_projection _ _ _ (openGluedProjection_transition C D i j) _ s

/-- On a common base open the actual ambient comparison carries one projection to the other. -/
@[reassoc]
lemma openGluedProjection_openTest (i j : ι) (U : X.Opens)
    (hi : U ≤ (C i).base.opensRange) (hj : U ≤ (C j).base.opensRange) :
    (pullback U.ι).map (openGluedProjection C D i) ≫
        (C i).ambientTestComparison (C j) D U.ι
          (coordinate (C i).base U hi) (coordinate (C j).base U hj)
          (coordinate_comp (C i).base U hi) (coordinate_comp (C j).base U hj) =
      (pullback U.ι).map (openGluedProjection C D j) := by
  apply pullback_projection_of_localEval
  intro V hV s
  have h := openGluedProjection_openTest_eval C D i j U hi hj V
    (hV.trans_eq U.opensRange_ι) s
  rw [Chart.openTestIso_eval] at h
  exact h

end FLT.Mazur.SchemeAffineDescent
