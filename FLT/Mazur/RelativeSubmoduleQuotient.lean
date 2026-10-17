/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Exact submodule quotients inside an ambient quotient

A quotient inside a submodule embeds in the ambient quotient. Flat scalar
extension preserves this embedding; localization clears an original denominator.
No assertion about tensoring this injection with a residue field is made.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.RelativeSubmoduleQuotient
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (N K : Submodule R M)

/-- The quotient of the exact submodule by the corrections it contains. -/
def inclusion : (N ⧸ K.comap N.subtype) →ₗ[R] M ⧸ K :=
  (K.comap N.subtype).mapQ K N.subtype le_rfl

/-- The comparison retains the original representative. -/
theorem inclusion_mk (x : N) :
    inclusion N K ((K.comap N.subtype).mkQ x) = K.mkQ x.val := rfl

/-- No relative class is lost when it is placed in the ambient quotient. -/
theorem inclusion_injective : Function.Injective (inclusion N K) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := (K.comap N.subtype).mkQ_surjective x
    change K.mkQ y.val = 0 at hx
    change (K.comap N.subtype).mkQ y = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (show y.val ∈ K from (Submodule.Quotient.mk_eq_zero K).mp hx)
  · exact bot_le

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Flat extension retains every relative class in the ambient quotient. -/
theorem baseChange_injective [Module.Flat R S] :
    Function.Injective ((inclusion N K).baseChange S) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ (inclusion_injective N K)

/-- Flat base change detects the relative class using the full ambient quotient. -/
theorem tmul_eq_zero_iff [Module.Flat R S] (x : N) :
    (1 ⊗ₜ[R] (K.comap N.subtype).mkQ x : S ⊗[R] (N ⧸ K.comap N.subtype)) = 0 ↔
      (1 ⊗ₜ[R] K.mkQ x.val : S ⊗[R] (M ⧸ K)) = 0 := by
  constructor
  · intro h
    have := congrArg ((inclusion N K).baseChange S) h
    simpa only [LinearMap.baseChange_tmul, inclusion_mk, map_zero] using this
  · intro h
    apply baseChange_injective N K S
    simpa only [LinearMap.baseChange_tmul, inclusion_mk, map_zero] using h

/-- Exact localization vanishing constructs one denominator in the original correction module. -/
theorem localized_mk_eq_zero_iff (U : Submonoid R) [IsLocalization U S] (x : N) :
    (1 ⊗ₜ[R] (K.comap N.subtype).mkQ x : S ⊗[R] (N ⧸ K.comap N.subtype)) = 0 ↔
      ∃ a : U, a.val • x.val ∈ K := by
  change TensorProduct.mk R S _ 1 ((K.comap N.subtype).mkQ x) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff U]
  simp only [Submonoid.smul_def, ← map_smul]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero (K.comap N.subtype)).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (Submodule.Quotient.mk_eq_zero (K.comap N.subtype)).mpr ha⟩

end FLT.Mazur.RelativeSubmoduleQuotient
