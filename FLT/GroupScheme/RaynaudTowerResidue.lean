/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTowerRootCharacter

/-!
# Compatible integral and residue embeddings for the tower

The prescribed fraction-field embedding lifts to the original integral closure.
Integrality proves that this map is local, so it induces a residue-field embedding.
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

variable {R L : Type*} [CommRing R] [IsLocalRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] [Algebra (v.adicCompletion K) L]
  [Algebra (v.adicCompletionIntegers K) R]
  [Algebra.IsIntegral (v.adicCompletionIntegers K) R]
  [Algebra (v.adicCompletionIntegers K) L]
  [IsScalarTower (v.adicCompletionIntegers K) R L]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) L]
  (e : L →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K))

/-- The prescribed tower embedding lifted to the original integral closure. -/
def towerIntegralMap : R →ₐ[O] Av :=
  { integralCoefficientMap (e.toRingHom.comp (algebraMap R L))
      (tower_coefficient_integral v e) with
    commutes' := fun a ↦ Subtype.ext (by
      change e (algebraMap R L (algebraMap O R a)) = algebraMap O Ωv a
      rw [← IsScalarTower.algebraMap_apply O R L]
      exact (e.restrictScalars O).commutes a) }

omit [IsLocalRing R] in
/-- The lifted embedding is injective. -/
theorem towerIntegralMap_injective : Function.Injective (towerIntegralMap v (R := R) e) := by
  intro a b h
  exact IsFractionRing.injective R L (e.injective (congrArg Subtype.val h))

/-- Integrality of the original closure makes the lifted embedding local. -/
instance towerIntegralMap_local : IsLocalHom (towerIntegralMap v (R := R) e).toRingHom := by
  let f := (towerIntegralMap v (R := R) e).toRingHom
  have hcomp : f.comp (algebraMap O R) = algebraMap O Av := by
    ext a
    exact (towerIntegralMap v (R := R) e).commutes a
  have hf : f.IsIntegral := RingHom.IsIntegral.tower_top (algebraMap O R) f
    (hcomp.symm ▸ algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral O Av))
  exact hf.isLocalHom (towerIntegralMap_injective v (R := R) e)

/-- The compatible residue-field embedding into the original closure's residue field. -/
def towerResidueMap : ResidueField R →+* ResidueField Av :=
  ResidueField.map (towerIntegralMap v (R := R) e).toRingHom

/-- Reduction commutes with the prescribed integral embedding. -/
theorem towerResidueMap_residue (a : R) :
    towerResidueMap v (R := R) e (residue R a) = residue Av (towerIntegralMap v (R := R) e a) :=
  ResidueField.map_residue _ a

end RaynaudParameters
