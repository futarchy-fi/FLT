/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Patching finitely many compatible principal ideal generators

Suppose each local ideal has finitely many ambient numerators. If a numerator
on the ith open belongs to every other local ideal after multiplication by
some power of the ith denominator, a single finite set of ambient relations
generates all the prescribed local ideals exactly. Denominators need only be
units in their own local rings; no global cover or noetherian hypothesis is used.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalIdealPatching

universe u v w

variable {P : Type u} [CommRing P] {ι : Type v} [Finite ι]

/-- Finitely many eventual ideal-membership conditions have a common denominator power. -/
theorem exists_pow_mem_all (r x : P) (K : ι → Ideal P)
    (h : ∀ i, ∃ n : ℕ, r ^ n * x ∈ K i) :
    ∃ n : ℕ, ∀ i, r ^ n * x ∈ K i := by
  classical
  let _ := Fintype.ofFinite ι
  choose n hn using h
  let N := Finset.univ.sup n
  refine ⟨N, fun i ↦ ?_⟩
  have hi : n i ≤ N := Finset.le_sup (f := n) (Finset.mem_univ i)
  have hm := (K i).mul_mem_left (r ^ (N - n i)) (hn i)
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi] using hm

variable {S : ι → Type w} [∀ i, CommRing (S i)]

/-- Compatible finite local generators can be represented by one finite ambient relation set. -/
theorem exists_finite_generators (I : Ideal P) (r : ι → P) (φ : ∀ i, P →+* S i)
    (hr : ∀ i, IsUnit (φ i (r i))) (J : ∀ i, Ideal (S i)) (s : ι → Finset P)
    (hsI : ∀ i, ∀ z ∈ s i, z ∈ I)
    (hs : ∀ i, Ideal.span ((φ i) '' (s i : Set P)) = J i)
    (hcompat : ∀ i, ∀ z ∈ s i, ∀ j, ∃ n : ℕ, φ j (r i ^ n * z) ∈ J j) :
    ∃ t : Finset P, (∀ z ∈ t, z ∈ I) ∧
      ∀ i, Ideal.span ((φ i) '' (t : Set P)) = J i := by
  classical
  let _ := Fintype.ofFinite ι
  let T := Σ i, {z // z ∈ s i}
  have h (k : T) : ∃ n : ℕ, ∀ j, φ j (r k.1 ^ n * k.2.val) ∈ J j :=
    exists_pow_mem_all (r k.1) k.2.val (fun j ↦ Ideal.comap (φ j) (J j))
      (hcompat k.1 k.2.val k.2.property)
  choose n hn using h
  let p (k : T) := r k.1 ^ n k * k.2.val
  let t := Finset.univ.image p
  have ht (k : T) : p k ∈ t := Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  refine ⟨t, ?_, fun i ↦ le_antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    exact I.mul_mem_left _ (hsI k.1 k.2.val k.2.property)
  · apply Ideal.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
    exact hn k i
  · rw [← hs i]
    apply Ideal.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    let k : T := ⟨i, z, hz⟩
    have hm : φ i (p k) ∈ Ideal.span ((φ i) '' (t : Set P)) :=
      Ideal.subset_span ⟨p k, ht k, rfl⟩
    change φ i (r i ^ n k * z) ∈ _ at hm
    rw [map_mul, map_pow, mul_comm] at hm
    exact (Ideal.mul_unit_mem_iff_mem _ ((hr i).pow (n k))).mp hm

end FLT.Mazur.PrincipalIdealPatching
