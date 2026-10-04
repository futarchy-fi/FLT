/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Denominators on arbitrary affine opens

The statements use the actual structure-sheaf restriction maps. No
Noetherian, reducedness, or finite type hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.AffineOpenDenominators
variable {X : Scheme.{u}} {U V : X.Opens}

/-- A function on a principal subopen has a numerator on the ambient affine open. -/
theorem exists_numerator (hU : IsAffineOpen U) (r : Γ(X, U)) (hV : V = X.basicOpen r)
    (a : Γ(X, V)) : ∃ (n : ℕ) (b : Γ(X, U)),
      X.presheaf.map (homOfLE (hV.trans_le (X.basicOpen_le r))).op b =
        X.presheaf.map (homOfLE (hV.trans_le (X.basicOpen_le r))).op r ^ n * a := by
  let i : V ⟶ U := homOfLE (hV.trans_le (X.basicOpen_le r))
  let :=  (X.presheaf.map i.op).hom.toAlgebra
  let :=  hU.isLocalization_of_eq_basicOpen r i hV
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj r a
  exact ⟨n, b, (mul_comm _ _).trans hb |>.symm⟩

/-- Vanishing after principal restriction is killed by a power, including on nonreduced schemes. -/
theorem zero_iff (hU : IsAffineOpen U) (r : Γ(X, U)) (hV : V = X.basicOpen r)
    (a : Γ(X, U)) :
    X.presheaf.map (homOfLE (hV.trans_le (X.basicOpen_le r))).op a = 0 ↔
      ∃ n : ℕ, r ^ n * a = 0 := by
  let i : V ⟶ U := homOfLE (hV.trans_le (X.basicOpen_le r))
  let :=  (X.presheaf.map i.op).hom.toAlgebra
  let :=  hU.isLocalization_of_eq_basicOpen r i hV
  change algebraMap Γ(X, U) Γ(X, V) a = 0 ↔ _
  rw [← map_zero (algebraMap Γ(X, U) Γ(X, V)), IsLocalization.eq_iff_exists (.powers r)]
  simp only [Submonoid.mem_powers_iff, Subtype.exists, exists_prop, exists_exists_eq_and,
    mul_zero]

/-- An existing numerator can be raised to any larger exponent. -/
lemma raise_numerator (r : Γ(X, U)) (h : V ≤ U) (a : Γ(X, V)) (b : Γ(X, U))
    {n N : ℕ} (hb : X.presheaf.map (homOfLE h).op b =
      X.presheaf.map (homOfLE h).op r ^ n * a) (hn : n ≤ N) :
    X.presheaf.map (homOfLE h).op (r ^ (N - n) * b) =
      X.presheaf.map (homOfLE h).op r ^ N * a := by
  rw [map_mul, map_pow, hb, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

/-- One exponent clears any finite dependent family of principal-open functions. -/
theorem finite_numerators {ι : Type*} [Finite ι] (U V : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (r : ∀ i, Γ(X, U i))
    (hV : ∀ i, V i = X.basicOpen (r i)) (a : ∀ i, Γ(X, V i)) :
    ∃ (N : ℕ) (b : ∀ i, Γ(X, U i)), ∀ i,
      X.presheaf.map (homOfLE ((hV i).trans_le (X.basicOpen_le (r i)))).op (b i) =
        X.presheaf.map (homOfLE ((hV i).trans_le (X.basicOpen_le (r i)))).op (r i) ^ N * a i := by
  classical
  let := Fintype.ofFinite ι
  choose n b hb using fun i ↦ exists_numerator (hU i) (r i) (hV i) (a i)
  refine ⟨Finset.univ.sup n, fun i ↦ r i ^ (Finset.univ.sup n - n i) * b i, fun i ↦ ?_⟩
  exact raise_numerator _ _ _ _ (hb i) (Finset.le_sup (Finset.mem_univ i))

/-- One power kills a finite dependent family of kernels of principal restrictions. -/
theorem finite_kernels {ι : Type*} [Finite ι] (U V : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (r a : ∀ i, Γ(X, U i))
    (hV : ∀ i, V i = X.basicOpen (r i))
    (ha : ∀ i, X.presheaf.map
      (homOfLE ((hV i).trans_le (X.basicOpen_le (r i)))).op (a i) = 0) :
    ∃ N : ℕ, ∀ i, r i ^ N * a i = 0 := by
  classical
  let := Fintype.ofFinite ι
  choose n hn using fun i ↦ (zero_iff (hU i) (r i) (hV i) (a i)).mp (ha i)
  refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
  have hi : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi, mul_zero] using
    congrArg (fun a ↦ r i ^ (Finset.univ.sup n - n i) * a) (hn i)

end FLT.Mazur.AffineOpenDenominators
