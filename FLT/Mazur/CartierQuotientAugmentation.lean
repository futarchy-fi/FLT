/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCartierQuotientIso

/-!
# Cartier quotient comparison from the original marking maps

Two augmentations to the same marking ring identify the original parameter
quotients. The full kernel equations and the actual commuting maps retain
scheme structure and multiplicity, without a reducedness assumption.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCartierComparison

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
local notation "f" => algebraMap R A

/-- The actual divisor quotient map is bijective when both kernels are the original parameter. -/
theorem parameterQuotientMap_bijective_of_augmentations (t : R)
    (ε : R →+* B) (δ : A →+* B) (hcomm : δ.comp (f) = ε)
    (hε : Function.Surjective ε) (hkerε : RingHom.ker ε = Ideal.span {t})
    (hkerδ : RingHom.ker δ = Ideal.span {f t}) :
    Function.Bijective (parameterQuotientMap (A := A) t) := by
  constructor
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    change parameterQuotientMap (A := A) t (Ideal.Quotient.mk _ a) = 0 at hz
    rw [parameterQuotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← hkerδ] at hz
    have he : ε a = 0 := (DFunLike.congr_fun hcomm a).symm.trans hz
    change Ideal.Quotient.mk _ a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hkerε]
    exact he
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hε (δ b)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [parameterQuotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hkerδ]
    change δ (f a - b) = 0
    rw [map_sub, ← RingHom.comp_apply, hcomm, ha, sub_self]

/-- Finite comparison across an original Cartier marking constructs the full algebra inverse. -/
theorem bijective_of_cartier_augmentations [IsNoetherianRing R] [Module.Finite R A]
    (t : R) (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hreg : f t ∈ nonZeroDivisors A)
    (ε : R →+* B) (δ : A →+* B) (hcomm : δ.comp (f) = ε)
    (hε : Function.Surjective ε) (hkerε : RingHom.ker ε = Ideal.span {t})
    (hkerδ : RingHom.ker δ = Ideal.span {f t}) : Function.Bijective (f) :=
  bijective_of_parameterQuotientMap t ht hreg
    (parameterQuotientMap_bijective_of_augmentations t ε δ hcomm hε hkerε hkerδ)

end FLT.Mazur.FiniteCartierComparison
