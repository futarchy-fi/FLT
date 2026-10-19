/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Ideal

/-!
# Evaluation ideals under localization

An evaluation extending to a localization has exactly the extended kernel.
This preserves the ideal itself, rather than only its radical or zero set.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizationEvaluationKernel

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  (e : R →+* T) (f : S →+* T) (h : ∀ x, f (algebraMap R S x) = e x)

include M h

/-- Localization carries the full evaluation ideal to the full extended evaluation ideal. -/
theorem ker_eq_map : RingHom.ker f = Ideal.map (algebraMap R S) (RingHom.ker e) := by
  have hc : (RingHom.ker f).under R = RingHom.ker e := by
    ext x
    change f (algebraMap R S x) = 0 ↔ e x = 0
    rw [h]
  rw [← IsLocalization.map_under M S (RingHom.ker f), hc]

/-- A principal evaluation ideal stays principal, with the same original generator. -/
theorem ker_eq_span (u : R) (hu : RingHom.ker e = Ideal.span {u}) :
    RingHom.ker f = Ideal.span {algebraMap R S u} := by
  rw [ker_eq_map M e f h, hu, Ideal.map_span, Set.image_singleton]

end FLT.Mazur.LocalizationEvaluationKernel
