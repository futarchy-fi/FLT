/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionOrderPoints
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Generic fibres and tensor evaluation of the odd-torsion coordinate order

The coordinate order is reduced because it is an algebra of functions into a
field. Localization and perfection imply that its generic fibre is finite étale.
These facts do not require an integral addition law.
-/

@[expose] public section

open scoped TensorProduct
universe u

namespace Algebra

/-- A finite reduced algebra over a perfect field is étale. -/
theorem etale_of_finite_reduced (K A : Type u) [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] : Etale K A := by
  let : IsArtinianRing A := .of_finite K A
  let (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  apply (Etale.iff_exists_algEquiv_prod K A).mpr
  exact ⟨MaximalSpectrum A, inferInstance, fun m => A ⧸ m.asIdeal,
    inferInstance, inferInstance, (IsArtinianRing.equivPi A).restrictScalars K,
    fun m => ⟨inferInstance, inferInstance⟩⟩

/-- The generic fibre of a reduced finite algebra over a domain is étale
when the fraction field is perfect. -/
theorem etale_genericFiber_of_finite_reduced (R K H : Type u)
    [CommRing R] [Field K] [PerfectField K] [Algebra R K]
    [IsFractionRing R K] [CommRing H] [Algebra R H]
    [Module.Finite R H] [IsReduced H] : Etale K (K ⊗[R] H) := by
  let : Algebra H (K ⊗[R] H) := TensorProduct.rightAlgebra
  let : IsReduced (K ⊗[R] H) :=
    isReduced_localizationPreserves (algebraMapSubmonoid H (nonZeroDivisors R)) _ inferInstance
  exact etale_of_finite_reduced K (K ⊗[R] H)

/-- Geometric points separate a flat algebra whose generic fibre is étale. -/
theorem eq_of_generic_points_eq (R K k H : Type u) [CommRing R] [Field K] [Field k]
    [Algebra R K] [Algebra R k] [Algebra K k] [IsScalarTower R K k]
    [IsFractionRing R K] [IsGalois K k] [IsSepClosed k]
    [CommRing H] [Algebra R H] [Module.Flat R H] [Etale K (K ⊗[R] H)]
    {x y : H} (h : ∀ f : H →ₐ[R] k, f x = f y) : x = y := by
  apply TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  apply (InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed K k (K ⊗[R] H)).1
  ext f
  exact h ((f.restrictScalars R).comp TensorProduct.includeRight)

/-- The tensor square of an algebra with étale generic fibre also has étale generic fibre. -/
theorem etale_genericFiber_tensorSquare (R K H : Type u) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [Algebra R H] [Etale K (K ⊗[R] H)] :
    Etale K (K ⊗[R] (H ⊗[R] H)) := by
  let e : ((K ⊗[R] H) ⊗[K] (K ⊗[R] H)) ≃ₐ[K] K ⊗[R] (H ⊗[R] H) :=
    (TensorProduct.tensorTensorTensorComm R R K K K H K H).trans
      (TensorProduct.congr (TensorProduct.lid K K)
        (AlgEquiv.refl : (H ⊗[R] H) ≃ₐ[R] (H ⊗[R] H)))
  let : Etale K ((K ⊗[R] H) ⊗[K] (K ⊗[R] H)) :=
    Etale.comp K (K ⊗[R] H) ((K ⊗[R] H) ⊗[K] (K ⊗[R] H))
  exact Etale.of_equiv e

end Algebra

namespace WeierstrassCurve
variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
    (W : WeierstrassCurve R) {n : ℕ} (hn : Odd n) (ξ η : R)
    (hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k η))
    (htwo : 2 • Affine.Point.some _ _ hT = 0)

/-- The odd-torsion coordinate order has finite étale generic fibre over a
perfect fraction field. This does not assume good reduction or coaddition. -/
theorem etale_oddTorsionCoordinateOrder_genericFiber
    [IsDedekindDomain R] [Module.IsTorsionFree R k]
    (K : Type u) [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K] :
    Algebra.Etale K (K ⊗[R] W.oddTorsionCoordinateOrder hn ξ η hT htwo) := by
  let H := W.oddTorsionCoordinateOrder hn ξ η hT htwo
  have hflat := W.finiteFlat_oddTorsionCoordinateOrder hn ξ η hT htwo
  let : Module.Finite R H := hflat.toFinite
  let : IsReduced H := isReduced_of_injective H.val Subtype.val_injective
  exact Algebra.etale_genericFiber_of_finite_reduced R K H

end WeierstrassCurve
