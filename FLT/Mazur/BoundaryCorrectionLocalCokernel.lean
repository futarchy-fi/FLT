/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFiniteCokernel

/-!
# Original local corrections at contractions of source primes

The ambient algebra is the localization of the original scalar ring at the
contracted source prime. Finite cokernel data construct a scalar whose image
avoids that source prime. These pointwise constructions give the source unit
ideal without assuming a global map from an ambient completion to the source.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  {T : Type*} [CommRing T] (κ : R →+* T) (P : Ideal T) [P.IsPrime]
set_option quotPrecheck false
local notation "S" => Localization.AtPrime (P.comap κ)
local notation "J" => IsLocalRing.maximalIdeal S
local notation "F" => ambientCorrectionOperator φ p q u S
local notation "π" => (LinearMap.range F).mkQ

/-- Finite cokernel data at the contracted prime construct an original source-local solution. -/
theorem localCokernel_source_solution
    (Q : Submodule S ((S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ⧸ LinearMap.range F))
    (hQ : Q.FG) (hred : Q ≤ J • Q)
    (hseed : π (ambientScalarError φ p q u S) ∈ Q) :
    ∃ y : correctionSolutions φ p q u, κ y.val.1 ∉ P := by
  let _ : Module.Flat R S := IsLocalization.flat S (P.comap κ).primeCompl
  obtain ⟨y, hy⟩ := finiteCokernel_original φ p q u S J Q hQ hred hseed J le_rfl
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  refine ⟨y, fun h ↦ hy ?_⟩
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S (P.comap κ) _).mpr h

local notation "I" => ideal (fun i ↦ algebraMap R (A i))
  (fun i ↦ (φ i).toRingHom) (fun i j ↦ (p i j).toRingHom)
  (fun i j ↦ (q i j).toRingHom)
  (fun i j r ↦ Eq.trans ((p i j).commutes r) (Eq.symm ((q i j).commutes r))) u

/-- The constructed original lifting multiplier avoids the source prime. -/
theorem localCokernel_source_multiplier
    (Q : Submodule S ((S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ⧸ LinearMap.range F))
    (hQ : Q.FG) (hred : Q ≤ J • Q)
    (hseed : π (ambientScalarError φ p q u S) ∈ Q) :
    ∃ a : R, a ∈ I ∧ κ a ∉ P := by
  obtain ⟨y, hy⟩ := localCokernel_source_solution φ p q u κ P Q hQ hred hseed
  exact ⟨y.val.1, correctionMultiplier_mem φ p q u y, hy⟩

omit [P.IsPrime] in
/-- Pointwise finite cokernel constructions at source maximal ideals generate the unit ideal. -/
theorem localCokernel_source_map_eq_top
    (h : ∀ (m : Ideal T) [m.IsMaximal],
      let Sₘ := Localization.AtPrime (m.comap κ)
      let Fₘ := ambientCorrectionOperator φ p q u Sₘ
      ∃ Q : Submodule Sₘ
          ((Sₘ ⊗[R] ((∀ i, B i) × ∀ i j, C i j)) ⧸ LinearMap.range Fₘ),
        Q.FG ∧ Q ≤ IsLocalRing.maximalIdeal Sₘ • Q ∧
          (LinearMap.range Fₘ).mkQ (ambientScalarError φ p q u Sₘ) ∈ Q) :
    (I).map κ = ⊤ := by
  by_contra hn
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal ((I).map κ) hn
  let _ := hm
  obtain ⟨Q, hQ, hred, hseed⟩ := h m
  obtain ⟨a, ha, hn⟩ := localCokernel_source_multiplier φ p q u κ m Q hQ hred hseed
  exact hn (hIm (Ideal.mem_map_of_mem κ ha))

end FLT.Mazur.BoundaryCorrectionIdeal
