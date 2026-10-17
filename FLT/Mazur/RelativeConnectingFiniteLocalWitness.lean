/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeBoundaryConnectingMap
public import FLT.Mazur.LocalizedImageFiniteWitness

/-!
# Finite original kernel corrections detect the full local relative image

Given finite generation of the local image, choose finitely many original
boundary values spanning it. Exact local vanishing is then equivalent to
boundary-zero corrections for those values with one common original denominator.
Finiteness and the actual corrections still have to be constructed geometrically.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.RelativeBoundaryConnectingMap
variable {R A B C D : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C) (N : Submodule R C)
  (β : D →ₗ[R] B) (u : D → A)
  (hb : ∀ t, b (u t) = β t) (hN : ∀ t, δ (u t) ∈ N)
  (U : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization U S]
set_option quotPrecheck false
local notation "K" => (LinearMap.ker b).map δ
local notation "g" => connecting b δ N β u hb hN

/-- An annihilated original relative value gives an exact original boundary-kernel correction. -/
theorem smul_connecting_eq_zero_iff (a : R) (t : D) :
    a • g t = 0 ↔ ∃ z : A, b z = 0 ∧ δ z = a • δ (u t) := by
  change a • ((K).comap N.subtype).mkQ ⟨δ (u t), hN t⟩ = 0 ↔ _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- A specified finite original spanning family needs only finitely many exact corrections. -/
theorem local_map_eq_zero_iff_finite_corrections {n : ℕ} (t : Fin n → D)
    (hspan : Submodule.span S (Set.range
      (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] (N ⧸ (K).comap N.subtype)))) =
        LinearMap.range ((g).baseChange S)) :
    (g).baseChange S = 0 ↔ ∃ (a : U) (z : Fin n → A),
      (∀ i, b (z i) = 0) ∧ (∀ i, δ (z i) = a.val • δ (u (t i))) := by
  rw [LocalizedImageFiniteWitness.baseChange_eq_zero_iff_common_annihilator U S g t hspan]
  constructor
  · rintro ⟨a, ha⟩
    have hz := fun i ↦ (smul_connecting_eq_zero_iff b δ N β u hb hN a.val (t i)).mp (ha i)
    choose z hbz hδz using hz
    exact ⟨a, z, hbz, hδz⟩
  · rintro ⟨a, z, hbz, hδz⟩
    exact ⟨a, fun i ↦ (smul_connecting_eq_zero_iff b δ N β u hb hN a.val (t i)).mpr
      ⟨z i, hbz i, hδz i⟩⟩

/-- Subtracting the finite corrections constructs compatible original numerator families. -/
theorem local_map_eq_zero_iff_finite_numerators {n : ℕ} (t : Fin n → D)
    (hspan : Submodule.span S (Set.range
      (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] (N ⧸ (K).comap N.subtype)))) =
        LinearMap.range ((g).baseChange S)) :
    (g).baseChange S = 0 ↔ ∃ (a : U) (v : Fin n → A),
      (∀ i, b (v i) = a.val • β (t i)) ∧ (∀ i, δ (v i) = 0) := by
  rw [local_map_eq_zero_iff_finite_corrections b δ N β u hb hN U S t hspan]
  constructor
  · rintro ⟨a, z, hbz, hδz⟩
    refine ⟨a, fun i ↦ a.val • u (t i) - z i, ?_, ?_⟩
    · intro i
      rw [map_sub, map_smul, hb, hbz, sub_zero]
    · intro i
      rw [map_sub, map_smul, hδz, sub_self]
  · rintro ⟨a, v, hbv, hδv⟩
    refine ⟨a, fun i ↦ a.val • u (t i) - v i, ?_, ?_⟩
    · intro i
      rw [map_sub, map_smul, hb, hbv, sub_self]
    · intro i
      rw [map_sub, map_smul, hδv, sub_zero]

/-- Local image finiteness constructs a finite test family of original boundary values. -/
theorem exists_finite_local_correction_test (hfg : (LinearMap.range ((g).baseChange S)).FG) :
    ∃ (n : ℕ) (t : Fin n → D),
      Submodule.span S (Set.range
        (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] (N ⧸ (K).comap N.subtype)))) =
          LinearMap.range ((g).baseChange S) ∧
      ((g).baseChange S = 0 ↔ ∃ (a : U) (z : Fin n → A),
        (∀ i, b (z i) = 0) ∧ (∀ i, δ (z i) = a.val • δ (u (t i)))) := by
  obtain ⟨n, t, ht⟩ := ScalarImageOriginalGenerators.exists_original_generators g S hfg
  exact ⟨n, t, ht, local_map_eq_zero_iff_finite_corrections b δ N β u hb hN U S t ht⟩

end FLT.Mazur.RelativeBoundaryConnectingMap
