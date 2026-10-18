/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalScalarFiniteLinearLifts
public import Mathlib.RingTheory.Localization.Module

/-!
# Localized surjectivity from finite original boundary generators

A scaled linear lift of the free generators lifts every fraction in their
span. When those generators span the boundary module, the localized boundary
map is surjective. No linear splitting of the boundary module is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalScalarGeneratedLocalizedLifts
variable {R A B I : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B] (N : Submodule R A) (β : A →ₗ[R] B)
  (S : Submonoid R) (t : I → B) (x : S) (L : (I →₀ R) →ₗ[R] N)
  (hL : (β.comp N.subtype).comp L = x.val • Finsupp.linearCombination R t)

include hL in
/-- Every fraction in the generated boundary span has a compatible source fraction. -/
theorem fraction_lift (b : B) (hb : b ∈ Submodule.span R (Set.range t)) (s : S) :
    ∃ w : N, LocalizedModule.map S (β.comp N.subtype)
      (LocalizedModule.mk w (x * s)) = LocalizedModule.mk b s := by
  obtain ⟨w, hw⟩ := OriginalScalarFiniteLinearLifts.span_lifts t x.val L hL b hb
  refine ⟨w, ?_⟩
  rw [LocalizedModule.map_mk]
  change LocalizedModule.mk (β w) (x * s) = LocalizedModule.mk b s
  rw [hw]
  exact LocalizedModule.mk_cancel_common_left x s b

include hL in
/-- Finite generator lifting suffices for surjectivity after original scalar localization. -/
theorem surjective_of_span (ht : Submodule.span R (Set.range t) = ⊤) :
    Function.Surjective (LocalizedModule.map S (β.comp N.subtype)) := by
  intro b
  induction b using LocalizedModule.induction_on with
  | _ b s =>
    obtain ⟨w, hw⟩ := fraction_lift N β S t x L hL b (ht ▸ Submodule.mem_top) s
    exact ⟨LocalizedModule.mk w (x * s), hw⟩

end FLT.Mazur.OriginalScalarGeneratedLocalizedLifts
