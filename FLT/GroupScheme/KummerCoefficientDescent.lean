/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerCoefficients
public import FLT.GroupScheme.KummerCocycle

/-!
# Root coefficients inside the finite cocycle field

The affine kernel fixes every coefficient, so its fixed field contains the
actual roots of unity. This identifies the descended action with the natural
field action needed by finite Hilbert 90.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {n : ℕ} [NeZero n] (c : Gal(L/K) → RootModule L n)
    (hc : groupCohomology.IsCocycle₁ c) (hcont : Continuous c)

local notation "E" => cocycleFixedField c hc hcont (continuous_root_orbit (K := K))

/-- All root coefficients lie in the finite fixed field of the affine kernel. -/
theorem root_mem_cocycleFixedField (x : RootModule L n) :
    (rootUnit x : L) ∈ (E).toIntermediateField := by
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  intro g hg
  have hx := ((mem_cocycleAction_ker c hc g).mp hg).2 x
  exact congrArg (fun z : RootModule L n ↦ (rootUnit z : L)) hx

/-- The coefficient embedding into units of the finite Galois field. -/
noncomputable def finiteRootUnit (x : RootModule L n) : Eˣ :=
  Units.mk0 ⟨rootUnit x, root_mem_cocycleFixedField c hc hcont x⟩
    (fun h ↦ (rootUnit x).ne_zero (congrArg Subtype.val h))

/-- The embedding retains the original root, not merely an abstract isomorphic group. -/
@[simp] theorem coe_finiteRootUnit (x : RootModule L n) :
    ((finiteRootUnit c hc hcont x : E) : L) = rootUnit x := rfl

/-- The finite-field coefficient embedding is injective. -/
theorem finiteRootUnit_injective : Function.Injective (finiteRootUnit c hc hcont) := by
  intro x y h
  apply rootUnit_injective
  apply Units.ext
  exact congrArg (fun u : Eˣ ↦ ((u : E) : L)) h

@[simp] theorem finiteRootUnit_add (x y : RootModule L n) :
    finiteRootUnit c hc hcont (x + y) =
      finiteRootUnit c hc hcont x * finiteRootUnit c hc hcont y := by
  apply Units.ext
  apply Subtype.ext
  rfl

/-- Embedded coefficients have the prescribed exponent. -/
theorem finiteRootUnit_pow (x : RootModule L n) : finiteRootUnit c hc hcont x ^ n = 1 := by
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun u : Lˣ ↦ (u : L)) (rootUnit_pow x)

/-- The transported action is the natural Galois action on embedded units. -/
theorem finiteRootUnit_smul (g : Gal(E/K)) (x : RootModule L n) :
    letI := finiteGaloisAction c hc hcont (continuous_root_orbit (K := K))
    finiteRootUnit c hc hcont (g • x) = g • finiteRootUnit c hc hcont x := by
  obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := E) L g
  calc
    _ = finiteRootUnit c hc hcont (s • x) := congrArg (finiteRootUnit c hc hcont)
      (finiteGaloisAction_restrict c hc hcont (continuous_root_orbit (K := K)) s x)
    _ = _ := by
      apply Units.ext
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes s E (finiteRootUnit c hc hcont x : E)).symm

/-- The descended root cocycle as a cocycle in finite-field units. -/
noncomputable def finiteUnitCocycle (g : Gal(E/K)) : Eˣ :=
  finiteRootUnit c hc hcont
    (finiteGaloisCocycle c hc hcont (continuous_root_orbit (K := K)) g)

/-- The coefficient embedding converts the additive cocycle identity to the multiplicative one. -/
theorem finiteUnitCocycle_isCocycle : groupCohomology.IsMulCocycle₁
    (finiteUnitCocycle c hc hcont) := by
  let := finiteGaloisAction c hc hcont (continuous_root_orbit (K := K))
  intro g h
  dsimp only [finiteUnitCocycle]
  rw [finiteGaloisCocycle_isCocycle, finiteRootUnit_add, finiteRootUnit_smul]

/-- Inflation of the embedded cocycle recovers the original field units. -/
theorem finiteUnitCocycle_restrict (g : Gal(L/K)) :
    ((finiteUnitCocycle c hc hcont (AlgEquiv.restrictNormalHom E g) : E) : L) =
      rootUnit (c g) := by
  simp only [finiteUnitCocycle, finiteGaloisCocycle_restrict, coe_finiteRootUnit]

end KummerTheory
