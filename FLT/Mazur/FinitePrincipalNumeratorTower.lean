/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalNumeratorTower
public import Mathlib.RingTheory.Ideal.Basic

/-!
# One denominator sequence for a finite family of compatible errors

The finite product of the actual boundary ideals retains all coordinates.
Finite suprema clear every equality and numerator simultaneously, so the
recursive construction uses one exponent at each order for the entire family.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FinitePrincipalNumeratorTower
variable {ι : Type*} [Finite ι]

private def piMap {R S : ι → Type*} [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
    (f : ∀ i, R i →+* S i) : (∀ i, R i) →+* (∀ i, S i) :=
  RingHom.pi (fun i ↦ (f i).comp (Pi.evalRingHom R i))

variable {R S : ι → ℕ → Type*}
  [∀ j k, CommRing (R j k)] [∀ j k, CommRing (S j k)]

/-- One monotone exponent sequence controls every coordinate of a finite family. -/
theorem exists_rescaled_tower
    (f : ∀ j k, R j k →+* S j k) (ρ : ∀ j k, R j (k + 1) →+* R j k)
    (σ : ∀ j k, S j (k + 1) →+* S j k)
    (hsq : ∀ j k z, f j k (ρ j k z) = σ j k (f j (k + 1) z))
    (r : ∀ j k, R j k) (hr : ∀ j k, ρ j k (r j (k + 1)) = r j k)
    (x : ∀ j k, S j k) (hx : ∀ j k, σ j k (x j (k + 1)) = x j k)
    (I : ∀ j k, Ideal (R j k))
    (hdetect : ∀ j k a b, f j k a = f j k b →
      ∃ d : ℕ, r j k ^ d * a = r j k ^ d * b)
    (hex : ∀ j k, ∃ (m : ℕ) (z : R j k), z ∈ I j k ∧
      f j k z = f j k (r j k) ^ m * x j k) :
    ∃ (N : ℕ → ℕ) (w : ∀ k j, R j k), Monotone N ∧
      (∀ k j, w k j ∈ I j k) ∧
      (∀ k j, f j k (w k j) = f j k (r j k) ^ N k * x j k) ∧
      ∀ k j, ρ j k (w (k + 1) j) = r j k ^ (N (k + 1) - N k) * w k j := by
  classical
  let _ := Fintype.ofFinite ι
  let F k := piMap (fun j ↦ f j k)
  have hd (k : ℕ) (a b : ∀ j, R j k) (h : F k a = F k b) :
      ∃ d : ℕ, (fun j ↦ r j k) ^ d * a = (fun j ↦ r j k) ^ d * b := by
    have hj (j : ι) := hdetect j k (a j) (b j) (congrFun h j)
    choose d hd using hj
    let L := Finset.univ.sup d
    refine ⟨L, funext (fun j ↦ ?_)⟩
    have hle : d j ≤ L := Finset.le_sup (Finset.mem_univ j)
    change r j k ^ L * a j = r j k ^ L * b j
    have he := congrArg (fun z ↦ r j k ^ (L - d j) * z) (hd j)
    simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle] using he
  have he (k : ℕ) : ∃ (m : ℕ) (z : ∀ j, R j k), z ∈ Ideal.pi (fun j ↦ I j k) ∧
      F k z = F k (fun j ↦ r j k) ^ m * (fun j ↦ x j k) := by
    choose m z hz he using fun j ↦ hex j k
    let L := Finset.univ.sup m
    refine ⟨L, fun j ↦ r j k ^ (L - m j) * z j,
      fun j ↦ (I j k).mul_mem_left _ (hz j), funext (fun j ↦ ?_)⟩
    exact PrincipalNumeratorTransition.promote (f j k) (r j k) (z j) (x j k)
      (Finset.le_sup (Finset.mem_univ j)) (he j)
  obtain ⟨N, w, hN, hw, he, ht⟩ := PrincipalNumeratorTower.exists_rescaled_tower F
    (fun k ↦ piMap (fun j ↦ ρ j k)) (fun k ↦ piMap (fun j ↦ σ j k))
    (fun k z ↦ funext (fun j ↦ hsq j k (z j))) (fun k j ↦ r j k)
    (fun k ↦ funext (fun j ↦ hr j k)) (fun k j ↦ x j k)
    (fun k ↦ funext (fun j ↦ hx j k)) (fun k ↦ Ideal.pi (fun j ↦ I j k)) hd he
  exact ⟨N, w, hN, hw, fun k j ↦ congrFun (he k) j, fun k j ↦ congrFun (ht k) j⟩

end FLT.Mazur.FinitePrincipalNumeratorTower
