/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Closed transitions on inverse images of a fixed open

Restricting a closed immersion to an exact inverse image is again closed.
Consequently the open restriction of a closed transition diagram retains
closed immersion transitions.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- A restriction along an equality of inverse images is a closed immersion. -/
theorem isClosedImmersion_resLE_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (U : Y.Opens) (V : X.Opens) (h : V = f ⁻¹ᵁ U) :
    IsClosedImmersion (f.resLE U V h.le) := by
  subst V
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- Closed immersion transitions remain closed on inverse images of a fixed open. -/
instance opensDiagram_map_isClosedImmersion {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    (i : I) (U : (D.obj i).Opens) {j k : Over i} (g : j ⟶ k) :
    IsClosedImmersion ((opensDiagram D i U).map g) := by
  apply isClosedImmersion_resLE_of_eq
  rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g]

end FLT.Mazur.Approximation
