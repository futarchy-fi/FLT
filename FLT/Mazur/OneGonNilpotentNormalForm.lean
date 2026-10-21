/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonInfinitesimalReduction

/-!
# Normal form across arbitrary nilpotent thickenings of the split node

Successive square-zero normalization and lifting of admissible changes give
an integral normal form for the original Weierstrass equation. The change
fixes its original reduction. No discriminant or small prime is inverted.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type*} [CommRing R]

/-- A subideal of a nilpotent ideal is nilpotent. -/
theorem nilpotent_of_le (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsNilpotent J) :
    IsNilpotent I := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  exact bot_unique ((pow_le_pow_left' hIJ n).trans (le_of_eq hn))

/-- Nilpotence survives every coefficient homomorphism. -/
theorem nilpotent_map (I : Ideal R) (hI : IsNilpotent I)
    {S : Type*} [CommRing S] (f : R →+* S) : IsNilpotent (I.map f) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]

/-- Every nilpotent deformation of the four nodal coefficients has a relative normal form. -/
theorem nilpotent_normalForm (W : WeierstrassCurve R) (I : Ideal R) (hI : IsNilpotent I)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) :
    ∃ (C : VariableChange R) (t : R), C • W = OneGonSmoothing.equation t ∧
      C.map (Ideal.Quotient.mk I) = 1 := by
  let P : ∀ {S : Type _} [CommRing S], Ideal S → Prop := fun {S} _ J =>
    IsNilpotent J → ∀ V : WeierstrassCurve S,
      V.a₁ + 1 ∈ J → V.a₂ ∈ J → V.a₃ ∈ J → V.a₄ ∈ J →
        ∃ (C : VariableChange S) (t : S), C • V = OneGonSmoothing.equation t ∧
          C.map (Ideal.Quotient.mk J) = 1
  have hP : P I := by
    apply Ideal.IsNilpotent.induction_on I hI
    · intro S _ J hJ _ V h₁ h₂ h₃ h₄
      exact squareZero_normalForm V J hJ h₁ h₂ h₃ h₄
    · intro S _ J K hJK hPJ hPK hK V h₁ h₂ h₃ h₄
      let q := Ideal.Quotient.mk J
      have hJ := nilpotent_of_le J K hJK hK
      obtain ⟨C₀, t₀, he₀, hc₀⟩ := hPK (nilpotent_map K hK q) (V.map q)
        (by simpa only [WeierstrassCurve.map, map_add, map_one] using
          Ideal.mem_map_of_mem q h₁)
        (Ideal.mem_map_of_mem q h₂) (Ideal.mem_map_of_mem q h₃)
        (Ideal.mem_map_of_mem q h₄)
      obtain ⟨C, hC⟩ := NilpotentVariableChange.exists_lift J hJ C₀
      have he : (C • V).map q = OneGonSmoothing.equation t₀ := by
        rw [← map_variableChange, hC, he₀]
      obtain ⟨ha, hb, hc, hd⟩ := coefficients_mem_of_map_eq (C • V) J t₀ he
      obtain ⟨D, t, heD, hcD⟩ := hPJ hJ (C • V) ha hb hc hd
      refine ⟨D * C, t, ?_, ?_⟩
      · simpa only [mul_smul] using heD
      · have hCK : C.map (Ideal.Quotient.mk K) = 1 := by
          apply NilpotentVariableChange.map_eq_one_of_quotient J K hJK
          rw [hC]
          exact hc₀
        have hDK := NilpotentVariableChange.map_eq_one_of_le J K hJK D hcD
        change VariableChange.mapHom (Ideal.Quotient.mk K) (D * C) = 1
        rw [map_mul]
        change D.map (Ideal.Quotient.mk K) * C.map (Ideal.Quotient.mk K) = 1
        rw [hDK, hCK, one_mul]
  exact hP hI W h₁ h₂ h₃ h₄

/-- A deformation of the nodal equation has a parameter in the original nilpotent ideal. -/
theorem nilpotent_normalForm_parameter (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    ∃ (C : VariableChange R) (t : R), C • W = OneGonSmoothing.equation t ∧
      C.map (Ideal.Quotient.mk I) = 1 ∧ t ∈ I := by
  obtain ⟨C, t, he, hc⟩ := nilpotent_normalForm W I hI h₁ h₂ h₃ h₄
  refine ⟨C, t, he, hc, ?_⟩
  have ht := I.add_mem (parameter_congr W I C t he hc) h₆
  simpa only [sub_add_cancel] using ht

end FLT.Mazur.OneGonInfinitesimal
