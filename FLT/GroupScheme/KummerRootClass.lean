/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerRefinement
public import FLT.GaloisRepresentation.Extensions.ContinuousClass
public import FLT.GroupScheme.KummerUnitClass

/-!
# Continuous classes of root ratios

A root of a base-field unit defines a continuous root-valued cocycle.
Multiplication of the root by a root of unity changes the splitting;
multiplication by a base-field unit leaves the cocycle unchanged.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {n : ℕ}

/-- A field unit with nth power one, regarded as an additive root coefficient. -/
def rootOfUnit (u : Lˣ) (hu : u ^ n = 1) : RootModule L n := Additive.ofMul ⟨u, hu⟩

@[simp] theorem rootUnit_rootOfUnit (u : Lˣ) (hu : u ^ n = 1) :
    rootUnit (rootOfUnit u hu) = u := rfl

/-- The ratio attached to a root of a base-field parameter. -/
def rootCocycle (q : Kˣ) (b : Lˣ) (hb : b ^ n = Units.map (algebraMap K L) q)
    (g : Gal(L/K)) : RootModule L n :=
  rootOfUnit (unitRatio b g) (by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, coe_unitRatio, Units.val_one]
    change (g (b : L) / (b : L)) ^ n = 1
    have hp := congrArg (fun u : Lˣ ↦ (u : L)) hb
    change (b : L) ^ n = algebraMap K L (q : K) at hp
    rw [div_pow, ← map_pow, hp, AlgEquiv.commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).mpr q.ne_zero)

omit [IsGalois K L] in
/-- Forgetting the root coefficient gives the usual ratio. -/
@[simp] theorem rootUnit_rootCocycle (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q) (g : Gal(L/K)) :
    rootUnit (rootCocycle q b hb g) = unitRatio b g := rfl

omit [IsGalois K L] in
/-- Root ratios obey the additive cocycle identity in the root module. -/
theorem rootCocycle_isCocycle (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q) :
    groupCohomology.IsCocycle₁ (rootCocycle q b hb) := by
  intro g h
  apply rootUnit_injective
  exact unitRatio_isCocycle b g h

/-- A root-ratio cocycle is locally constant for the Krull topology. -/
theorem continuous_rootCocycle (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q) : Continuous (rootCocycle q b hb) := by
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  refine ⟨{h : Gal(L/K) | h (b : L) = g (b : L)},
    ContinuousSMulDiscrete.isOpen_smul_eq Gal(L/K) _ _, rfl, ?_⟩
  intro h hh
  apply rootUnit_injective
  apply Units.ext
  simpa only [rootUnit_rootCocycle, coe_unitRatio] using
    congrArg (fun x : L ↦ x / (b : L)) hh

/-- A root-ratio cocycle bundled with continuity. -/
def continuousRootCocycle (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q) :
    ContinuousCocycle Gal(L/K) (RootModule L n) :=
  ⟨⟨rootCocycle q b hb, continuous_rootCocycle q b hb⟩, rootCocycle_isCocycle q b hb⟩

omit [IsGalois K L] in
/-- Multiplying a root by a root coefficient gives exactly a splitting change. -/
theorem rootCocycle_mul_root (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q) (x : RootModule L n)
    (hd : (b * rootUnit x) ^ n = Units.map (algebraMap K L) q) :
    rootCocycle q (b * rootUnit x) hd = changeSplitting (rootCocycle q b hb) x := by
  funext g
  apply rootUnit_injective
  change unitRatio (b * rootUnit x) g = unitRatio b g * unitRatio (rootUnit x) g
  exact unitRatio_mul b (rootUnit x) g

/-- Different roots of the same parameter yield the same continuous class. -/
theorem continuousRootCocycle_independent (q : Kˣ) (b d : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q)
    (hd : d ^ n = Units.map (algebraMap K L) q) :
    continuousClassMk (continuousRootCocycle q b hb) =
      continuousClassMk (continuousRootCocycle q d hd) := by
  apply (continuousClassMk_eq_iff _ _).mpr
  let x : RootModule L n := rootOfUnit (d / b) (by rw [div_pow, hd, hb, div_self'])
  refine ⟨x, funext fun g ↦ ?_⟩
  apply rootUnit_injective
  change unitRatio d g = unitRatio b g * (g • (d / b) / (d / b))
  simp only [unitRatio, smul_div']
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

end KummerTheory
