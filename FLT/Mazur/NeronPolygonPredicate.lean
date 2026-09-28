/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingDiagram
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Néron polygons as cyclic pinchings over the base field

A scheme over `K` is an `n`-gon when it is the pushout of the specified cyclic
pinching span, in the category of schemes over `Spec K`. This is a property of
an actual scheme with its structure morphism. It does not construct a pushout
or require a pushout-existence instance. For `n = 1` the span pinches zero and
infinity on a single projective line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur

variable {K : Type u} [Field K]

/-- An `n`-gon is a realization of the specified cyclic pinching as a pushout over `K`. -/
def IsNeronNGon (C : Over (Spec (CommRingCat.of K))) (n : ℕ) (hn : 0 < n) : Prop :=
  ∃ (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C),
    IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q

/-- A Néron polygon has a positive number of components and the cyclic pinching property. -/
def IsNeronPolygon (C : Over (Spec (CommRingCat.of K))) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n), IsNeronNGon C n hn

namespace IsNeronNGon

variable {C C' : Over (Spec (CommRingCat.of K))} {n : ℕ} {hn : 0 < n}

/-- Transport a realization of the pinching span along an isomorphism over `K`. -/
theorem of_iso (h : IsNeronNGon C n hn) (e : C ≅ C') : IsNeronNGon C' n hn := by
  obtain ⟨p, q, hpq⟩ := h
  refine ⟨p ≫ e.hom, q ≫ e.hom, ?_⟩
  exact hpq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)

/-- Being the specified `n`-gon is invariant under isomorphism over the base. -/
theorem iso_iff (e : C ≅ C') : IsNeronNGon C n hn ↔ IsNeronNGon C' n hn :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Every realization with a positive number of components is a Néron polygon. -/
theorem isNeronPolygon (h : IsNeronNGon C n hn) : IsNeronPolygon C := ⟨n, hn, h⟩

end IsNeronNGon

namespace IsNeronPolygon

variable {C C' : Over (Spec (CommRingCat.of K))}

/-- Transport the polygon property along an isomorphism over `K`. -/
theorem of_iso (h : IsNeronPolygon C) (e : C ≅ C') : IsNeronPolygon C' := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, hn, h.of_iso e⟩

/-- The polygon property is invariant under isomorphism over the base. -/
theorem iso_iff (e : C ≅ C') : IsNeronPolygon C ↔ IsNeronPolygon C' :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

end IsNeronPolygon

end FLT.Mazur
