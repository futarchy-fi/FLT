/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderSection

/-!
# Order of base-field elements in the unramified union

The constructed order on the union extends the DVR order on its base
fraction field, by integral-unit and uniformizer factorization.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

local notation "U" => maximalUnramified R K C

/-- The union's order restricts to the base's normalized integer order. -/
theorem unramifiedUnionOrder_base (x : Kˣ) :
    unramifiedUnionOrder R K C (Units.map (algebraMap K U).toMonoidHom x) =
      discreteOrder R K x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨u, n, rfl⟩ := exists_unit_mul_fractionUniformizer_zpow R K hπ x
  have hu : Units.map (algebraMap K U).toMonoidHom (Units.map (algebraMap R K) u) =
      Units.map (algebraMap (integralClosure R U) U).toMonoidHom
        (Units.map (algebraMap R (integralClosure R U)).toMonoidHom u) := by
    apply Units.ext
    change algebraMap K U (algebraMap R K (u : R)) =
      algebraMap (integralClosure R U) U (algebraMap R (integralClosure R U) (u : R))
    simp only [← IsScalarTower.algebraMap_apply]
  rw [map_mul, map_mul, map_zpow, hu, unramifiedUnionOrder_integralUnit, one_mul,
    map_zpow, map_mul, discreteOrder_unit, one_mul, map_zpow,
    discreteOrder_fractionUniformizer]
  exact congrArg (fun z => z ^ n) (unramifiedUnionOrder_uniformizer R K C hπ)

end LocalClassFieldTheory
