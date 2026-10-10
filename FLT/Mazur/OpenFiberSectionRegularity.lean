/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSectionMonicity
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Restricting a regular fiber section to its actual source chart

Pasting the chart and family squares constructs an open immersion into the
family fiber. Monicity then passes to the original section pulled first to
the source chart and then to its independently constructed base change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.OpenFiberSectionRegularity
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {P U X T S : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ S) (g : T ⟶ S)
  {p : P ⟶ U} {q : P ⟶ T} (h : IsPullback p q (j ≫ f) g)

/-- The chart base change maps into the actual family fiber product. -/
def toFiber : P ⟶ pullback f g := pullback.lift (p ≫ j) q (by
  simpa only [Category.assoc] using h.w)

/-- This map is the base change of the original source chart. -/
theorem toFiber_isPullback : IsPullback (toFiber j f g h) p (pullback.fst f g) j := by
  have H : IsPullback (toFiber j f g h ≫ pullback.snd f g) p g (j ≫ f) := by
    simpa only [toFiber, pullback.lift_snd] using h.flip
  exact H.of_right (by simp [toFiber]) (IsPullback.of_hasPullback f g).flip

/-- An open source chart induces an open immersion into the actual fiber. -/
instance [IsOpenImmersion j] : IsOpenImmersion (toFiber j f g h) :=
  IsOpenImmersion.of_isPullback (toFiber_isPullback j f g h).flip inferInstance

include h in
/-- Fiber regularity supplies monicity of the independently pulled chart section. -/
theorem chart_mono [IsOpenImmersion j] (M : X.Modules) (s : Γ(M, ⊤))
    [Mono (globalSectionHom _ (pullGlobal (pullback.fst f g) M s))] :
    Mono (globalSectionHom _ (pullGlobal p _ (pullGlobal j M s))) := by
  apply (OpenSectionMonicity.comp_iff p j M s).mp
  exact OpenSectionMonicity.composite_mono (toFiber j f g h) (pullback.fst f g)
    (p ≫ j) (by simp [toFiber]) M s

end FLT.Mazur.OpenFiberSectionRegularity
