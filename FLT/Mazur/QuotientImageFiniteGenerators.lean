/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite quotient images give finite compatible numerator families

Finiteness of an image modulo corrections is equivalent to finitely many
numerators generating its preimage modulo those corrections. The chosen
numerators belong to the prescribed compatible submodule, not merely the
ambient equation module. The correction module itself need not be finite.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.QuotientImageFiniteGenerators
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (K H : Submodule R M) (hKH : K ≤ H)

include hKH in
/-- Finite generators of the quotient image lift to compatible original numerators. -/
theorem exists_numerators (hfg : (H.map K.mkQ).FG) :
    ∃ (n : ℕ) (v : Fin n → M), (∀ i, v i ∈ H) ∧
      K ⊔ Submodule.span R (Set.range v) = H := by
  obtain ⟨n, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hmem : ∀ i, w i ∈ H.map K.mkQ := fun i ↦ hw ▸ Submodule.subset_span ⟨i, rfl⟩
  choose v hv he using hmem
  refine ⟨n, v, hv, ?_⟩
  have hmap : (Submodule.span R (Set.range v)).map K.mkQ = H.map K.mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact (congrArg (fun w : Fin n → M ⧸ K ↦ Submodule.span R (Set.range w))
      (funext he)).trans hw
  have hc := congrArg (Submodule.comap K.mkQ) hmap
  simpa only [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hKH,
    sup_comm] using hc

include hKH in
/-- An exact finite numerator criterion, without requiring a finite correction module. -/
theorem fg_iff_exists_numerators :
    (H.map K.mkQ).FG ↔ ∃ (n : ℕ) (v : Fin n → M),
      (∀ i, v i ∈ H) ∧ K ⊔ Submodule.span R (Set.range v) = H := by
  constructor
  · exact exists_numerators K H hKH
  · rintro ⟨n, v, _, hgen⟩
    rw [← hgen, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    exact (Submodule.fg_span (Set.finite_range v)).map _

include hKH in
/-- The same criterion with the finite numerator submodule kept as an object. -/
theorem fg_iff_exists_relative_submodule :
    (H.map K.mkQ).FG ↔ ∃ E : Submodule R M, E.FG ∧ K ⊔ E = H := by
  constructor
  · intro h
    obtain ⟨n, v, _, hgen⟩ := exists_numerators K H hKH h
    exact ⟨_, Submodule.fg_span (Set.finite_range v), hgen⟩
  · rintro ⟨E, hE, hgen⟩
    rw [← hgen, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    exact hE.map _

end FLT.Mazur.QuotientImageFiniteGenerators
