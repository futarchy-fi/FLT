/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerRefinement

/-!
# Finite Hilbert 90 for continuous root cocycles

Descend a continuous cocycle to its finite Galois field, apply finite
Hilbert 90 there, and include the resulting root into the original field.
No infinite version of Hilbert 90 or parameter-existence premise is used.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {n : ℕ} [NeZero n] (c : Gal(L/K) → RootModule L n)
    (hc : groupCohomology.IsCocycle₁ c) (hcont : Continuous c)

include hc hcont

/-- Every continuous root cocycle has a nonzero base parameter and a root upstairs. -/
theorem exists_continuous_kummer_parameter :
    ∃ a : K, ∃ b : L, a ≠ 0 ∧ b ≠ 0 ∧ b ^ n = algebraMap K L a ∧
      ∀ g : Gal(L/K), g b = (rootUnit (c g) : L) * b := by
  let E := cocycleFixedField c hc hcont (continuous_root_orbit (K := K))
  obtain ⟨a, b, ha, hb, hpow, heq⟩ := exists_kummer_parameter
    (finiteUnitCocycle c hc hcont) (finiteUnitCocycle_isCocycle c hc hcont)
    (fun g ↦ finiteRootUnit_pow c hc hcont _)
  refine ⟨a, (b : L), ha, fun h ↦ hb (Subtype.ext h), ?_, ?_⟩
  · exact congrArg (fun x : E ↦ (x : L)) hpow
  · intro g
    have h := congrArg (fun x : E ↦ (x : L)) (heq (AlgEquiv.restrictNormalHom E g))
    change ((AlgEquiv.restrictNormalHom E g b : E) : L) =
      ((finiteUnitCocycle c hc hcont (AlgEquiv.restrictNormalHom E g) : E) : L) *
        (b : L) at h
    rw [AlgEquiv.restrictNormalHom_apply, finiteUnitCocycle_restrict] at h
    exact h

/-- The same parameter theorem expressed entirely in unit groups. -/
theorem exists_continuous_unit_parameter :
    ∃ q : Kˣ, ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L) q ∧
      ∀ g : Gal(L/K), unitRatio b g = rootUnit (c g) := by
  obtain ⟨a, b, ha, hb, hpow, heq⟩ := exists_continuous_kummer_parameter c hc hcont
  refine ⟨Units.mk0 a ha, Units.mk0 b hb, Units.ext hpow, fun g ↦ ?_⟩
  apply Units.ext
  rw [coe_unitRatio]
  change g b / b = (rootUnit (c g) : L)
  exact (div_eq_iff hb).mpr (heq g)

end KummerTheory
