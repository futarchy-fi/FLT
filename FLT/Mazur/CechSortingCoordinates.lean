/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechComplex
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Integral signed sorting of Cech coordinates

Stable sorting gives a permutation sign. Deleting an entry commutes with
sorting, with the corresponding integral coface sign.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace FLT.Mazur.CechSortingCoordinates

open IncreasingCechComplex

variable {ι : Type u} [LinearOrder ι]

/-- Sorting and then deleting is deleting and then sorting, including repetitions. -/
lemma sort_face_reindex {n : ℕ} (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (Tuple.sort a j).succAbove ∘ Tuple.sort (a ∘ (Tuple.sort a j).succAbove) =
      Tuple.sort a ∘ j.succAbove := by
  let σ := Tuple.sort a
  let e := σ * j.cycleRange.symm
  obtain ⟨⟨k, τ⟩, hτ⟩ := (Equiv.Perm.decomposeFin'Symm_uncurry_bijective n).surjective e
  have hk : k = σ j := by
    simpa [e] using DFunLike.congr_fun hτ 0
  subst k
  have he (i : Fin (n + 1)) : (σ j).succAbove (τ i) = σ (j.succAbove i) := by
    simpa [e] using DFunLike.congr_fun hτ i.succ
  have hs := (Tuple.eq_sort_iff (f := a) (σ := σ)).mp rfl
  have ht : τ = Tuple.sort (a ∘ (σ j).succAbove) := by
    apply Tuple.eq_sort_iff.mpr
    constructor
    · intro r s hrs
      simpa only [Function.comp_apply, he] using
        hs.1 ((Fin.strictMono_succAbove j).monotone hrs)
    · intro r s hrs h
      apply (Fin.strictMono_succAbove (σ j)).lt_iff_lt.mp
      rw [he, he]
      exact hs.2 _ _ (Fin.strictMono_succAbove j hrs)
        (by simpa only [Function.comp_apply, he] using h)
  rw [← ht]
  exact funext he

/-- The sorted face has the same values as the corresponding face of the sorted tuple. -/
lemma sorted_face {n : ℕ} (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (a ∘ (Tuple.sort a j).succAbove) ∘ Tuple.sort (a ∘ (Tuple.sort a j).succAbove) =
      (a ∘ Tuple.sort a) ∘ j.succAbove := by
  rw [Function.comp_assoc, sort_face_reindex]
  rfl

/-- Deletion changes the sorting sign by exactly the two coface signs. -/
lemma sign_sort_face {n : ℕ} (a : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (Tuple.sort a j).val *
        (Equiv.Perm.sign (Tuple.sort (a ∘ (Tuple.sort a j).succAbove)) : ℤ) =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) * (-1 : ℤ) ^ j.val := by
  have he : Equiv.Perm.decomposeFin'Symm (Tuple.sort a j)
      (Tuple.sort (a ∘ (Tuple.sort a j).succAbove)) = Tuple.sort a * j.cycleRange.symm := by
    apply Equiv.ext
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using congrFun (sort_face_reindex a j) i
  have h := congrArg (fun e ↦ (Equiv.Perm.sign e : ℤ)) he
  simpa only [Equiv.Perm.sign_decomposeFin'Symm, map_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Equiv.Perm.sign_symm,
    Fin.sign_cycleRange] using h

/-- Sort an injective tuple into an increasing tuple. -/
def sortTuple {n : ℕ} (a : Fin (n + 1) → ι) (h : Function.Injective a) :
    IncreasingCechComplex.Tuple (ι := ι) n :=
  ⟨a ∘ Tuple.sort a,
    (Tuple.monotone_sort a).strictMono_of_injective (h.comp (Tuple.sort a).injective)⟩

omit [LinearOrder ι] in
/-- Deleting either of two equal adjacent entries gives the same tuple. -/
lemma adjacent_face_eq {n : ℕ} (a : Fin (n + 2) → ι) (p : Fin (n + 1))
    (h : a p.castSucc = a p.succ) :
    a ∘ p.castSucc.succAbove = a ∘ p.succ.succAbove := by
  funext i
  rcases lt_trichotomy i p with hi | rfl | hi
  · simp [Fin.succAbove_castSucc_of_lt _ _ hi, Fin.succAbove_succ_of_le _ _ hi.le]
  · simpa using h.symm
  · simp [Fin.succAbove_castSucc_of_le _ _ hi.le, Fin.succAbove_succ_of_lt _ _ hi]

omit [LinearOrder ι] in
/-- A face retaining a repeated pair is still noninjective. -/
lemma face_not_injective {n : ℕ} (a : Fin (n + 2) → ι) {i j k : Fin (n + 2)}
    (hij : i ≠ j) (h : a i = a j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Function.Injective (a ∘ k.succAbove) := by
  obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hik
  obtain ⟨s, hs⟩ := Fin.exists_succAbove_eq hjk
  intro hinj
  apply hij
  rw [← hr, ← hs]
  exact congrArg k.succAbove (hinj (by simpa only [Function.comp_apply, hr, hs] using h))

variable {X : TopCat.{u}} (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

omit [LinearOrder ι] in
/-- Permuting indices leaves the tuple intersection unchanged. -/
lemma perm_le {n : ℕ} (a : Fin (n + 1) → ι) (σ : Equiv.Perm (Fin (n + 1))) :
    CechSheafHZero.V U n a ≤ CechSheafHZero.V U n (a ∘ σ) :=
  le_iInf fun j ↦ iInf_le _ (σ j)

/-- Signed sorting of sections, with zero on every repeated tuple. -/
def signedSort (n : ℕ) (x : Term U F n) (a : Fin (n + 1) → ι) :
    F.obj.obj (op (CechSheafHZero.V U n a)) :=
  if h : Function.Injective a then
    (Equiv.Perm.sign (Tuple.sort a) : ℤ) •
      F.obj.map (homOfLE (perm_le U a (Tuple.sort a))).op (x (sortTuple a h))
  else 0

lemma signedSort_of_not_injective (n : ℕ) (x : Term U F n) (a : Fin (n + 1) → ι)
    (h : ¬ Function.Injective a) : signedSort U F n x a = 0 := by
  rw [signedSort, dite_eq_right h]

lemma signedSort_of_injective (n : ℕ) (x : Term U F n) (a : Fin (n + 1) → ι)
    (h : Function.Injective a) :
    signedSort U F n x a = (Equiv.Perm.sign (Tuple.sort a) : ℤ) •
      F.obj.map (homOfLE (perm_le U a (Tuple.sort a))).op (x (sortTuple a h)) := by
  rw [signedSort, dite_eq_left h]

/-- Equal increasing tuples give equal restricted coordinates. -/
lemma coordinate_congr {n : ℕ} (x : Term U F n)
    {a b : IncreasingCechComplex.Tuple (ι := ι) n} (h : a = b) {W : Opens X}
    (ha : op (CechSheafHZero.V U n a.val) ⟶ op W)
    (hb : op (CechSheafHZero.V U n b.val) ⟶ op W) :
    F.obj.map ha (x a) = F.obj.map hb (x b) := by
  subst b
  rw [Subsingleton.elim ha hb]

/-- On increasing tuples signed sorting recovers the original coordinate. -/
lemma signedSort_increasing (n : ℕ) (x : Term U F n)
    (a : IncreasingCechComplex.Tuple (ι := ι) n) : signedSort U F n x a.val = x a := by
  rw [signedSort_of_injective U F n x a.val a.property.injective]
  have hs := Tuple.sort_eq_refl_iff_monotone.mpr a.property.monotone
  have ht : sortTuple a.val a.property.injective = a := by
    apply Subtype.ext
    simp [sortTuple, hs]
  have hsign : (Equiv.Perm.sign (Tuple.sort a.val) : ℤ) = 1 := by simp [hs]
  rw [hsign, one_smul]
  erw [coordinate_congr U F x ht _ (𝟙 _)]
  change F.obj.map (𝟙 _) (x a) = x a
  rw [F.obj.map_id]
  rfl

/-- An increasing face coordinate, extended by zero to other faces. -/
def faceCoordinate (n : ℕ) (x : Term U F n) (a : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    F.obj.obj (op (CechSheafHZero.V U (n + 1) a)) :=
  if h : StrictMono (a ∘ k.succAbove) then
    F.obj.map (homOfLE (face_le U n a k)).op (x ⟨a ∘ k.succAbove, h⟩)
  else 0

/-- Sorting identifies the restriction coordinates of corresponding faces. -/
lemma signedSort_face (n : ℕ) (x : Term U F n) (a : Fin (n + 2) → ι)
    (j : Fin (n + 2)) :
    (-1 : ℤ) ^ (Tuple.sort a j).val •
        F.obj.map (homOfLE (face_le U n a (Tuple.sort a j))).op
          (signedSort U F n x (a ∘ (Tuple.sort a j).succAbove)) =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) • (-1 : ℤ) ^ j.val •
        F.obj.map (homOfLE (perm_le U a (Tuple.sort a))).op
          (faceCoordinate U F n x (a ∘ Tuple.sort a) j) := by
  let b := a ∘ (Tuple.sort a j).succAbove
  have he := sorted_face a j
  by_cases hb : Function.Injective b
  · have hc : StrictMono ((a ∘ Tuple.sort a) ∘ j.succAbove) := by
      rw [← he]
      exact (sortTuple b hb).property
    rw [signedSort_of_injective U F n x _ hb, faceCoordinate, dite_eq_left hc]
    simp only [map_zsmul, smul_smul]
    congr 1
    · exact sign_sort_face a j
    · simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      have ht : sortTuple b hb = ⟨(a ∘ Tuple.sort a) ∘ j.succAbove, hc⟩ := Subtype.ext he
      exact coordinate_congr U F x ht _ _
  · have hc : ¬ StrictMono ((a ∘ Tuple.sort a) ∘ j.succAbove) := by
      intro hc
      apply hb
      have hi : Function.Injective (b ∘ Tuple.sort b) := by
        rw [he]
        exact hc.injective
      exact hi.of_comp_right (Tuple.sort b).surjective
    rw [signedSort_of_not_injective U F n x _ hb, faceCoordinate, dite_eq_right hc]
    simp

/-- Identical deleted tuples give identical extended face coordinates. -/
lemma faceCoordinate_eq (n : ℕ) (x : Term U F n) (a : Fin (n + 2) → ι)
    (i j : Fin (n + 2)) (h : a ∘ i.succAbove = a ∘ j.succAbove) :
    faceCoordinate U F n x a i = faceCoordinate U F n x a j := by
  by_cases hi : StrictMono (a ∘ i.succAbove)
  · have hj : StrictMono (a ∘ j.succAbove) := h ▸ hi
    rw [faceCoordinate, dite_eq_left hi, faceCoordinate, dite_eq_left hj]
    have ht : (⟨a ∘ i.succAbove, hi⟩ : IncreasingCechComplex.Tuple (ι := ι) n) =
        ⟨a ∘ j.succAbove, hj⟩ := Subtype.ext h
    exact coordinate_congr U F x ht _ _
  · have hj : ¬ StrictMono (a ∘ j.succAbove) := fun hj ↦ hi (h.symm ▸ hj)
    rw [faceCoordinate, dite_eq_right hi, faceCoordinate, dite_eq_right hj]

/-- Equal adjacent entries cancel in the integral alternating face sum. -/
lemma faceCoordinate_sum_of_adjacent_eq (n : ℕ) (x : Term U F n)
    (a : Fin (n + 2) → ι) (p : Fin (n + 1)) (h : a p.castSucc = a p.succ) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • faceCoordinate U F n x a k = 0 := by
  have hp : p.castSucc ≠ p.succ := (Fin.castSucc_lt_succ (i := p)).ne
  rw [Fintype.sum_eq_add _ _ hp (fun k hk ↦ ?_)]
  · rw [faceCoordinate_eq U F n x a _ _ (adjacent_face_eq a p h)]
    simp [pow_succ]
  · have hn : ¬ StrictMono (a ∘ k.succAbove) := fun hc ↦
      face_not_injective a hp h hk.1.symm hk.2.symm hc.injective
    rw [faceCoordinate, dite_eq_right hn, smul_zero]

/-- A sorted tuple with repetitions has zero alternating face sum. -/
lemma faceCoordinate_sum_of_not_injective (n : ℕ) (x : Term U F n)
    (a : Fin (n + 2) → ι) (hm : Monotone a) (ha : ¬ Function.Injective a) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • faceCoordinate U F n x a k = 0 := by
  have hn : ¬ StrictMono a := fun h ↦ ha h.injective
  rw [Fin.strictMono_iff_lt_succ, not_forall] at hn
  obtain ⟨p, hp⟩ := hn
  exact faceCoordinate_sum_of_adjacent_eq U F n x a p
    (le_antisymm (hm (Fin.castSucc_lt_succ (i := p)).le) (not_lt.mp hp))

/-- On an increasing tuple the extended face sum is the actual differential. -/
lemma faceCoordinate_sum_increasing (n : ℕ) (x : Term U F n)
    (a : IncreasingCechComplex.Tuple (ι := ι) (n + 1)) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • faceCoordinate U F n x a.val k =
      differential U F n x a := by
  rw [differential_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [faceCoordinate, dite_eq_left (a.property.comp (Fin.strictMono_succAbove k))]
  rfl

/-- Reindex the full signed face sum using the sorting permutation. -/
lemma signedSort_face_sum (n : ℕ) (x : Term U F n) (a : Fin (n + 2) → ι) :
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val • F.obj.map (homOfLE (face_le U n a k)).op
        (signedSort U F n x (a ∘ k.succAbove)) =
      (Equiv.Perm.sign (Tuple.sort a) : ℤ) •
        F.obj.map (homOfLE (perm_le U a (Tuple.sort a))).op
          (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
            faceCoordinate U F n x (a ∘ Tuple.sort a) j) := by
  rw [← Equiv.sum_comp (Tuple.sort a)]
  simp_rw [signedSort_face]
  simp only [map_sum, map_zsmul, Finset.smul_sum]

/-- Signed sorting commutes with the coordinate differential, integrally in every degree. -/
lemma signedSort_differential (n : ℕ) (x : Term U F n) (a : Fin (n + 2) → ι) :
    signedSort U F (n + 1) (differential U F n x) a =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
        F.obj.map (homOfLE (face_le U n a k)).op
          (signedSort U F n x (a ∘ k.succAbove)) := by
  rw [signedSort_face_sum]
  by_cases ha : Function.Injective a
  · rw [signedSort_of_injective U F (n + 1) _ a ha]
    congr 2
    exact (faceCoordinate_sum_increasing U F n x (sortTuple a ha)).symm
  · rw [signedSort_of_not_injective U F (n + 1) _ a ha]
    have hs : ¬ Function.Injective (a ∘ Tuple.sort a) :=
      fun h ↦ ha (h.of_comp_right (Tuple.sort a).surjective)
    rw [faceCoordinate_sum_of_not_injective U F n x _ (Tuple.monotone_sort a) hs,
      map_zero, smul_zero]

end FLT.Mazur.CechSortingCoordinates
