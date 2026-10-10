/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilies

/-!
# Cartesian intersections of relative ideal ambients

A cartesian square of parameter schemes induces a cartesian square of their
actual ambient pullbacks. This identifies chart intersections before ideal descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A S W X Y Z : Scheme.{u}} (a : A ⟶ S)
variable (s : Z ⟶ S) (t : X ⟶ S) (r : Y ⟶ S) (q : W ⟶ S)
variable (f : X ⟶ Z) (g : Y ⟶ Z) (u : W ⟶ X) (v : W ⟶ Y)
variable (hf : f ≫ s = t) (hg : g ≫ s = r) (hu : u ≫ t = q) (hv : v ≫ r = q)

/-- Base change of a cartesian parameter square gives the full ambient intersection. -/
theorem relativeIdealAmbientMap_square_isPullback (h : IsPullback u v f g) :
    IsPullback (relativeIdealAmbientMap a t q u hu) (relativeIdealAmbientMap a r q v hv)
      (relativeIdealAmbientMap a s t f hf) (relativeIdealAmbientMap a s r g hg) := by
  have hw : relativeIdealAmbientMap a t q u hu ≫ relativeIdealAmbientMap a s t f hf =
      relativeIdealAmbientMap a r q v hv ≫ relativeIdealAmbientMap a s r g hg := by
    rw [relativeIdealAmbientMap_comp, relativeIdealAmbientMap_comp]
    congr 1
    exact h.w
  have hp := (relativeIdealAmbientMap_isPullback a t q u hu).paste_vert h
  rw [← relativeIdealAmbientMap_fst a r q v hv,
    ← relativeIdealAmbientMap_fst a s t f hf] at hp
  exact hp.of_bot hw (relativeIdealAmbientMap_isPullback a s r g hg)

end FLT.Mazur.ClosedIdealCover
