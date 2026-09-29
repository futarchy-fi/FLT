/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingHomotopyCoordinates

/-!
# Signed sorting of integral tuple chains

Sorting with its permutation sign, and killing repeated tuples, commutes with
alternating deletion. The augmentation and singleton maps are identities, and
sorting preserves the set of vertices supporting a chain.
-/

@[expose] public noncomputable section

open scoped BigOperators

universe u

namespace FLT.Mazur.CechSortingTupleChains

open CechSortingHomotopyCoordinates CechSortingCoordinates

variable {ι : Type u} [LinearOrder ι]

/-- The signed sorted generator, zero on tuples with repeated entries. -/
def signedGenerator {n : ℕ} (a : Fin n → ι) : Chains (ι := ι) n :=
  if Function.Injective a then
    (Equiv.Perm.sign (Tuple.sort a) : ℤ) • FreeAbelianGroup.of (a ∘ Tuple.sort a)
  else 0

/-- Integral signed sorting, including the augmentation term. -/
def P (n : ℕ) : Chains (ι := ι) n →+ Chains (ι := ι) n :=
  FreeAbelianGroup.lift signedGenerator

@[simp]
lemma P_of {n : ℕ} (a : Fin n → ι) :
    P n (FreeAbelianGroup.of a) = signedGenerator a :=
  FreeAbelianGroup.lift_apply_of _ _

lemma signedGenerator_of_injective {n : ℕ} (a : Fin n → ι)
    (ha : Function.Injective a) :
    signedGenerator a =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) • FreeAbelianGroup.of (a ∘ Tuple.sort a) := by
  rw [signedGenerator, ite_eq_left ha]

lemma signedGenerator_of_not_injective {n : ℕ} (a : Fin n → ι)
    (ha : ¬ Function.Injective a) : signedGenerator a = 0 := by
  rw [signedGenerator, ite_eq_right ha]

/-- On increasing tuples sorting fixes the generator. -/
lemma signedGenerator_of_strictMono {n : ℕ} (a : Fin n → ι) (ha : StrictMono a) :
    signedGenerator a = FreeAbelianGroup.of a := by
  rw [signedGenerator_of_injective a ha.injective,
    Tuple.sort_eq_refl_iff_monotone.mpr ha.monotone]
  simp

/-- Signed sorting fixes the empty tuple chain. -/
@[simp]
lemma P_zero (z : Chains (ι := ι) 0) : P 0 z = z := by
  have h : P (ι := ι) 0 = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro a
    simp only [P_of, AddMonoidHom.id_apply]
    exact signedGenerator_of_strictMono a (fun i ↦ Fin.elim0 i)
  exact DFunLike.congr_fun h z

/-- Signed sorting fixes every singleton chain. -/
@[simp]
lemma P_one (z : Chains (ι := ι) 1) : P 1 z = z := by
  have h : P (ι := ι) 1 = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro a
    simp only [P_of, AddMonoidHom.id_apply]
    exact signedGenerator_of_strictMono a (fun i j hij ↦ by
      have : i = j := Subsingleton.elim _ _
      subst j
      exact (lt_irrefl _ hij).elim)
  exact DFunLike.congr_fun h z

/-- An increasing generator, extended by zero to the other tuples. -/
def increasingGenerator {n : ℕ} (a : Fin n → ι) : Chains (ι := ι) n :=
  if StrictMono a then FreeAbelianGroup.of a else 0

/-- Sorting matches face generators with the integral deletion signs. -/
lemma signedGenerator_face (n : ℕ) (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (Tuple.sort a j).val •
        signedGenerator (a ∘ (Tuple.sort a j).succAbove) =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) • (-1 : ℤ) ^ j.val •
        increasingGenerator ((a ∘ Tuple.sort a) ∘ j.succAbove) := by
  let b := a ∘ (Tuple.sort a j).succAbove
  have he := sorted_face a j
  by_cases hb : Function.Injective b
  · have hc : StrictMono ((a ∘ Tuple.sort a) ∘ j.succAbove) := by
      rw [← he]
      exact (sortTuple b hb).property
    rw [signedGenerator_of_injective _ hb, increasingGenerator, ite_eq_left hc]
    rw [he, smul_smul, smul_smul, sign_sort_face]
  · have hc : ¬ StrictMono ((a ∘ Tuple.sort a) ∘ j.succAbove) := by
      intro hc
      apply hb
      have hi : Function.Injective (b ∘ Tuple.sort b) := by
        rw [he]
        exact hc.injective
      exact hi.of_comp_right (Tuple.sort b).surjective
    rw [signedGenerator_of_not_injective _ hb, increasingGenerator, ite_eq_right hc]
    simp

/-- Adjacent repeated entries cancel in the extended integral face sum. -/
lemma increasingGenerator_sum_of_adjacent_eq (n : ℕ) (a : Fin (n + 2) → ι)
    (p : Fin (n + 1)) (h : a p.castSucc = a p.succ) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • increasingGenerator (a ∘ k.succAbove) = 0 := by
  have hp : p.castSucc ≠ p.succ := (Fin.castSucc_lt_succ (i := p)).ne
  rw [Fintype.sum_eq_add _ _ hp (fun k hk ↦ ?_)]
  · rw [adjacent_face_eq a p h]
    simp [pow_succ]
  · have hn : ¬ StrictMono (a ∘ k.succAbove) := fun hc ↦
      face_not_injective a hp h hk.1.symm hk.2.symm hc.injective
    rw [increasingGenerator, ite_eq_right hn, smul_zero]

/-- Sorting turns any repeated pair into an adjacent cancellation. -/
lemma increasingGenerator_sum_of_not_injective (n : ℕ) (a : Fin (n + 2) → ι)
    (hm : Monotone a) (ha : ¬ Function.Injective a) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • increasingGenerator (a ∘ k.succAbove) = 0 := by
  have hn : ¬ StrictMono a := fun h ↦ ha h.injective
  rw [Fin.strictMono_iff_lt_succ, not_forall] at hn
  obtain ⟨p, hp⟩ := hn
  exact increasingGenerator_sum_of_adjacent_eq n a p
    (le_antisymm (hm (Fin.castSucc_lt_succ (i := p)).le) (not_lt.mp hp))

/-- Reindex the signed sorted face sum along the sorting permutation. -/
lemma signedGenerator_face_sum (n : ℕ) (a : Fin (n + 2) → ι) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • signedGenerator (a ∘ k.succAbove) =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) •
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
          increasingGenerator ((a ∘ Tuple.sort a) ∘ j.succAbove) := by
  rw [← Equiv.sum_comp (Tuple.sort a)]
  simp_rw [signedGenerator_face]
  rw [Finset.smul_sum]

/-- Signed sorting commutes with deletion on generators of length at least two. -/
lemma boundary_signedGenerator (n : ℕ) (a : Fin (n + 2) → ι) :
    boundary (n + 1) (signedGenerator a) =
      P (n + 1) (boundary (n + 1) (FreeAbelianGroup.of a)) := by
  rw [boundary_of, map_sum]
  simp only [map_zsmul, P_of]
  rw [signedGenerator_face_sum]
  by_cases ha : Function.Injective a
  · rw [signedGenerator_of_injective a ha, map_zsmul, boundary_of]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj : StrictMono ((a ∘ Tuple.sort a) ∘ j.succAbove) :=
      (sortTuple a ha).property.comp (Fin.strictMono_succAbove j)
    rw [increasingGenerator, ite_eq_left hj]
  · rw [signedGenerator_of_not_injective a ha, map_zero]
    have hs : ¬ Function.Injective (a ∘ Tuple.sort a) :=
      fun h ↦ ha (h.of_comp_right (Tuple.sort a).surjective)
    rw [increasingGenerator_sum_of_not_injective n _ (Tuple.monotone_sort a) hs,
      smul_zero]

/-- Integral signed sorting is a chain map, including the augmentation boundary. -/
lemma boundary_P (n : ℕ) (z : Chains (ι := ι) (n + 1)) :
    boundary n (P (n + 1) z) = P n (boundary n z) := by
  cases n with
  | zero => simp
  | succ n =>
    have h : (boundary (ι := ι) (n + 1)).comp (P (n + 2)) =
        (P (n + 1)).comp (boundary (n + 1)) := by
      apply FreeAbelianGroup.lift_ext
      intro a
      simp only [AddMonoidHom.comp_apply, P_of]
      exact boundary_signedGenerator n a
    exact DFunLike.congr_fun h z

omit [LinearOrder ι] in
/-- Permuting the entries of a supported generator preserves support. -/
lemma permuted_of_mem_supported (S : Set ι) (n : ℕ) (a : Fin n → ι)
    (ha : ∀ i, a i ∈ S) (σ : Equiv.Perm (Fin n)) :
    FreeAbelianGroup.of (a ∘ σ) ∈ supported S n :=
  of_mem_supported S n _ (fun i ↦ ha (σ i))

/-- Sorting a supported generator preserves support, also when it vanishes. -/
lemma signedGenerator_mem_supported (S : Set ι) (n : ℕ) (a : Fin n → ι)
    (ha : ∀ i, a i ∈ S) : signedGenerator a ∈ supported S n := by
  by_cases hi : Function.Injective a
  · rw [signedGenerator_of_injective a hi]
    exact (supported S n).zsmul_mem (permuted_of_mem_supported S n a ha (Tuple.sort a)) _
  · rw [signedGenerator_of_not_injective a hi]
    exact (supported S n).zero_mem

/-- Signed sorting preserves the vertex support of every integral chain. -/
lemma P_mem_supported (S : Set ι) (n : ℕ) (z : Chains (ι := ι) n)
    (hz : z ∈ supported S n) : P n z ∈ supported S n := by
  have h : supported S n ≤ (supported S n).comap (P n) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨a, ha, rfl⟩
    change P n (FreeAbelianGroup.of a) ∈ supported S n
    rw [P_of]
    exact signedGenerator_mem_supported S n a ha
  exact h hz

end FLT.Mazur.CechSortingTupleChains
