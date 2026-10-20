/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCyclotomicOrbit
public import FLT.Mazur.RootsOfUnityCartier
public import FLT.Mazur.AffineSpectrumKernelIdeal

/-!
# The full cyclotomic orbit as an equality of scheme ideals

The integral orbit equation identifies the actual subgroup ideal with the
product of the actual specialized unit-section kernels, including multiplicities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.CyclotomicSchemeOrbit

open BaseAdicThickening IntegralCyclotomicCoordinates

/-- The affine ideal-sheaf construction preserves every finite ideal product. -/
theorem baseIdeal_prod {ι : Type*} (R : CommRingCat) (s : Finset ι) (I : ι → Ideal R) :
    baseIdeal R (∏ i ∈ s, I i) = ∏ i ∈ s, baseIdeal R (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [baseIdeal_top, Ideal.map_top]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ← ih]
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [baseIdeal_top, Ideal.map_mul]

/-- The specialized cyclotomic orbit cuts out the entire roots-of-unity scheme. -/
theorem ideal {R : Type*} [CommRing R] (n : ℕ) [NeZero n]
    (φ : Coordinate n →+* R) :
    RootsOfUnityCartier.ideal R n = ∏ i : Fin n,
      (Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R)
        ((Units.map φ.toMonoidHom (rootUnit n)) ^ i.val)).toRingHom)).ker := by
  simp only [RootsOfUnityCartier.ideal, RootsOfUnityScheme.inclusion_left,
    specMap_ker_baseIdeal]
  change baseIdeal (.of R[T;T⁻¹])
      (RingHom.ker (RootsOfUnityAlgebra.restriction R n).toAlgHom.toRingHom) =
    ∏ i : Fin n, baseIdeal (.of R[T;T⁻¹])
      (RingHom.ker (LaurentUnitPoints.evalUnit (R := R)
        ((Units.map φ.toMonoidHom (rootUnit n)) ^ i.val)).toRingHom)
  rw [IntegralCyclotomicOrbit.kernel_unit_orbit n φ, baseIdeal_prod]

end FLT.Mazur.CyclotomicSchemeOrbit
