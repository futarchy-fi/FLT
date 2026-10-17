/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SubmoduleReductionFlat
public import FLT.Mazur.FiniteLocalSpanVanishing

/-!
# Nakayama with the reduction kernel retained

Ambient residual vanishing kills a finite error submodule only after the
reduced inclusion has been proved injective. A flat quotient is one sufficient
input. Finiteness of the whole ambient module is never assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] (Q : Submodule R M)

/-- Injective reduction turns ambient residual vanishing into a valid Nakayama argument. -/
theorem eq_bot_of_reduced_inclusion (hQ : Q.FG)
    (hinj : Function.Injective
      (SubmoduleReduction.inclusion (IsLocalRing.maximalIdeal R) Q))
    (hzero : Q ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) : Q = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal R) Q hQ
    (SubmoduleReduction.le_smul_of_inclusion_injective _ Q hinj hzero)
    (IsLocalRing.maximalIdeal_le_jacobson _)

/-- A flat quotient supplies the missing injectivity for the same finite-module argument. -/
theorem eq_bot_of_residual_of_flat_quotient [Module.Flat R (M ⧸ Q)] (hQ : Q.FG)
    (hzero : Q ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) : Q = ⊥ :=
  eq_bot_of_reduced_inclusion Q hQ
    (SubmoduleReduction.inclusion_injective_of_flat_quotient _ Q) hzero

variable {N : Type*} [AddCommGroup N] [Module R N] (g : N →ₗ[R] M)

/-- For a map it suffices to check ambient residual vanishing on a spanning family. -/
theorem range_le_smul_top_of_generators {ι : Type*} (v : ι → N)
    (hv : Submodule.span R (Set.range v) = ⊤)
    (hzero : ∀ i, g (v i) ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    LinearMap.range g ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  rw [← Submodule.map_top, ← hv, Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hzero i

/-- A finite image with injective reduction and vanishing reduced generators is zero. -/
theorem map_eq_zero_of_reduced_generators (hfg : (LinearMap.range g).FG)
    (hinj : Function.Injective
      (SubmoduleReduction.inclusion (IsLocalRing.maximalIdeal R) (LinearMap.range g)))
    {ι : Type*} (v : ι → N) (hv : Submodule.span R (Set.range v) = ⊤)
    (hzero : ∀ i, g (v i) ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) : g = 0 := by
  apply LinearMap.range_eq_bot.mp
  exact eq_bot_of_reduced_inclusion _ hfg hinj
    (range_le_smul_top_of_generators g v hv hzero)

end FLT.Mazur.FiniteErrorReduction
