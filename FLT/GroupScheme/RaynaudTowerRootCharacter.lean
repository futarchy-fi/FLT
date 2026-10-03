/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIntegralCoordinateCharacter
public import FLT.GroupScheme.RaynaudTowerClosure

/-!
# Root characters after prescribed closure placement

Transport an actual root equation and its integral coefficients to the original
closure, where the original inertia root-character theorem applies.
-/

@[expose] public noncomputable section
namespace RaynaudParameters
open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure Kv
local notation "Av" => IntegralClosure O Ωv

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] [Algebra (v.adicCompletion K) L]
  (e : L →ₐ[(v.adicCompletion K)] AlgebraicClosure (v.adicCompletion K))

/-- Integral tower coefficients remain integral under the prescribed embedding. -/
theorem tower_coefficient_integral [Algebra O R] [Algebra.IsIntegral O R]
    [Algebra O L] [IsScalarTower O R L] [IsScalarTower O Kv L] (r : R) :
    IsIntegral O (e (algebraMap R L r)) := by
  exact ((Algebra.IsIntegral.isIntegral (R := O) r).map
    (IsScalarTower.toAlgHom O R L)).map (e.restrictScalars O)

/-- Transported prime-power equations give integral original-inertia character ratios. -/
theorem exists_tower_coordinate_ratio
    (hf : ∀ r : R, IsIntegral O (e (algebraMap R L r)))
    {p n m : ℕ} (hp : (p : Kv) ≠ 0) (hn : 0 < n)
    {α : Ωv} (hα : α ^ n = algebraMap Kv Ωv (p : Kv))
    (u : Rˣ) {x : AlgebraicClosure L}
    (hx : x ^ n = algebraMap R (AlgebraicClosure L) ((p : R) ^ m * u))
    (σ : localInertiaGroup v) :
    ∃ r : Av, r.val = σ.1 (towerClosureEquiv e x) / towerClosureEquiv e x ∧
      residue Av r = (LocalRoot.character v hn hp hα σ : ResidueField Av) ^ m := by
  apply exists_integral_coordinate_ratio v
    (e.toRingHom.comp (algebraMap R L)) hf hn hp hα u
  have h := congrArg (towerClosureEquiv e) hx
  simpa only [map_pow, map_mul, map_natCast, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    IsScalarTower.algebraMap_apply R L (AlgebraicClosure L),
    towerClosureEquiv_algebraMap] using h

end RaynaudParameters
