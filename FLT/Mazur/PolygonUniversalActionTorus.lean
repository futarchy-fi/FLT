/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonUniversalAction
public import FLT.Mazur.ProjectiveLineActionTorus

/-!
# The original whole-polygon action on full normalization tori

Both Laurent parameters remain variable. The original universal action is
multiplication on the torus followed by the specified cyclic component inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
namespace FLT.Mazur.PolygonUniversalAction
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
variable {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- On full normalization tori the original action is the actual torus group law. -/
@[reassoc] theorem torus_act (a : ZMod n) (i : Fin n) :
    (PolygonSplitGroup.component K n a ⊗ₘ (torusToComponent K ≫ componentι K n i ≫ p)) ≫
        act K n hn p q h =
      μ[MultiplicativeGroupScheme.gm K] ≫ torusToComponent K ≫
        componentι K n (rotateIndex a i) ≫ p := by
  rw [← whiskerLeft_comp_tensorHom_assoc, component_act,
    ProjectiveLineActionTorus.torus_act_assoc]

end FLT.Mazur.PolygonUniversalAction
