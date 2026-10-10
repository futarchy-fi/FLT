/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersion descent along specified cartesian charts

The criterion accepts actual pullback squares, avoiding the need to replace
the chosen chart schemes by the category's chosen pullbacks in applications.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v

/-- Closed immersion can be checked on any cartesian family over a target open cover. -/
theorem isClosedImmersion_of_cartesian_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.OpenCover.{v}) (A : V.I₀ → Scheme.{u})
    (p : ∀ i, A i ⟶ X) (q : ∀ i, A i ⟶ V.X i)
    (h : ∀ i, IsPullback (p i) (q i) f (V.f i))
    (hq : ∀ i, IsClosedImmersion (q i)) : IsClosedImmersion f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) V
  intro i
  let _ := hq i
  exact (congrArg (fun k ↦ IsClosedImmersion k) (h i).isoPullback_inv_snd).mp
    (IsClosedImmersion.comp (h i).isoPullback.inv (q i))

end FLT.Mazur
