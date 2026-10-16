/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite denominators from the original scalar ring

Localize different coefficient rings at images of one multiplicative set.
Finite families of fractions and equalities can be cleared by one element of
that original set. No injectivity of any localization map is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteBaseLocalizationDenominators
variable {R : Type*} [CommRing R] (M : Submonoid R)
  {ι : Type*} [Finite ι]

/-- Finitely many denominators divide one denominator in the original multiplicative set. -/
theorem exists_common_multiple (d : ι → M) :
    ∃ s : M, ∀ i, ∃ u : M, s = u * d i := by
  classical
  let _ := Fintype.ofFinite ι
  refine ⟨∏ i, d i, fun i ↦ ?_⟩
  obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  exact ⟨u, hu.trans (mul_comm _ _)⟩

variable {A S : ι → Type*} [∀ i, CommRing (A i)] [∀ i, CommRing (S i)]
  (α : ∀ i, R →+* A i) [∀ i, Algebra (A i) (S i)]
  [∀ i, IsLocalization (M.map (α i).toMonoidHom) (S i)]

omit [Finite ι] in
/-- A fraction has a denominator coming from the original ring, even for a noninjective map. -/
theorem exists_numerator (i : ι) (v : S i) :
    ∃ s : M, ∃ a : A i,
      algebraMap (A i) (S i) a = algebraMap (A i) (S i) (α i s) * v := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M.map (α i).toMonoidHom) v
  obtain ⟨r, hr, he⟩ := s.property
  refine ⟨⟨r, hr⟩, a, ?_⟩
  change α i r = s.val at he
  change algebraMap (A i) (S i) a = algebraMap (A i) (S i) (α i r) * v
  rw [he, mul_comm]
  exact hs.symm

/-- One original scalar clears a finite family of fractions in unrelated coefficient rings. -/
theorem exists_numerators (v : ∀ i, S i) :
    ∃ s : M, ∃ a : ∀ i, A i, ∀ i,
      algebraMap (A i) (S i) (a i) = algebraMap (A i) (S i) (α i s) * v i := by
  choose d a ha using fun i ↦ exists_numerator M α i (v i)
  obtain ⟨s, hs⟩ := exists_common_multiple M d
  choose u hu using hs
  refine ⟨s, fun i ↦ α i (u i) * a i, fun i ↦ ?_⟩
  rw [map_mul, ha i, hu i]
  simp only [Submonoid.coe_mul, map_mul, mul_assoc]

omit [Finite ι] in
/-- One localized equality is killed by the image of an original allowed denominator. -/
theorem exists_equality (i : ι) (a b : A i)
    (h : algebraMap (A i) (S i) a = algebraMap (A i) (S i) b) :
    ∃ s : M, α i s * a = α i s * b := by
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists (M.map (α i).toMonoidHom) (S i)).mp h
  obtain ⟨r, hr, he⟩ := s.property
  change α i r = s.val at he
  exact ⟨⟨r, hr⟩, by change α i r * a = α i r * b; rw [he]; exact hs⟩

/-- Finite localized equations become exact after multiplication by one original denominator. -/
theorem exists_equalities (a b : ∀ i, A i)
    (h : ∀ i, algebraMap (A i) (S i) (a i) = algebraMap (A i) (S i) (b i)) :
    ∃ s : M, ∀ i, α i s * a i = α i s * b i := by
  choose d hd using fun i ↦ exists_equality M α i (a i) (b i) (h i)
  obtain ⟨s, hs⟩ := exists_common_multiple M d
  choose u hu using hs
  refine ⟨s, fun i ↦ ?_⟩
  rw [hu i]
  simp only [Submonoid.coe_mul, map_mul, mul_assoc, hd i]

end FLT.Mazur.FiniteBaseLocalizationDenominators
