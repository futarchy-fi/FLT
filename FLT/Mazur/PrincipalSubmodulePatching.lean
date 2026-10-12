/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite intersections and denominator clearing for arbitrary localization models

These lemmas work with the actual coefficient tensor maps, without replacing them
by the canonical localized-module type. A finite compatible family is effective
once compatibility supplies numerator denominator clearing.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalSubmodulePatching
variable {A B V W : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
  [Module B W] [IsScalarTower A B W]
  (S : Submonoid A) [IsLocalization S B] (g : V →ₗ[A] W) [IsLocalizedModule S g]

/-- Numerator membership in any localization model clears a denominator in the base. -/
theorem numerator_mem_iff (P : Submodule A V) (x : V) :
    g x ∈ P.localized' B S g ↔ ∃ s : S, (s : A) • x ∈ P := by
  constructor
  · rintro ⟨y, hy, s, hs⟩
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists S g).mp hs
    refine ⟨t * s, ?_⟩
    rw [Submonoid.coe_mul, mul_smul]
    change (t : A) • y = (t : A) • (s : A) • x at ht
    rw [← ht]
    exact P.smul_mem _ hy
  · rintro ⟨s, hs⟩
    exact ⟨(s : A) • x, hs, s, IsLocalizedModule.mk'_cancel g x s⟩

/-- Localization commutes with finite intersections in any localization model. -/
theorem localized_iInf {ι : Type*} [Finite ι] (P : ι → Submodule A V) :
    (⨅ i, P i).localized' B S g = ⨅ i, (P i).localized' B S g := by
  let _ : Fintype ι := Fintype.ofFinite ι
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Function.comp_apply,
    Submodule.IsLocalizedModule.localized'FrameHom_apply] using
    map_finset_inf (Submodule.localized'FrameHom B S g) Finset.univ P

omit [IsLocalization S B] [IsLocalizedModule S g] in
/-- Powers of a unit-ideal cover detect membership in any submodule. -/
theorem mem_of_cover_powers {ι : Type*} (r : ι → A)
    (hr : Ideal.span (Set.range r) = ⊤) (P : Submodule A V) (x : V)
    (hx : ∀ i, ∃ n : ℕ, r i ^ n • x ∈ P) : x ∈ P := by
  apply P.mem_of_span_eq_top_of_smul_pow_mem (Set.range r) hr x
  rintro ⟨_, i, rfl⟩
  exact hx i

/-- Finite numerator compatibility recovers the given submodule on a principal chart. -/
theorem localized_iInf_eq {ι : Type*} [Finite ι] (P : ι → Submodule A V)
    (N : Submodule B W) (i : ι)
    (hi : P i = Submodule.comap g (N.restrictScalars A))
    (h : ∀ j x, x ∈ P i → ∃ s : S, (s : A) • x ∈ P j) :
    (⨅ j, P j).localized' B S g = N := by
  rw [localized_iInf]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq
      (hi ▸ (Submodule.localized'gi B S g).l_u_eq N)
  · apply le_iInf
    intro j
    rw [← (Submodule.localized'gi B S g).l_u_eq N]
    apply (Submodule.localized'gi B S g).gc _ _ |>.mpr
    intro x hx
    exact (numerator_mem_iff (B := B) S g (P j) x).mpr (h j x (hi ▸ hx))

end FLT.Mazur.PrincipalSubmodulePatching
