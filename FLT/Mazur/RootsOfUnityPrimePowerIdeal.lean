/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityPrimePowerOrbit
public import FLT.Mazur.RootsOfUnityCartier
public import FLT.Mazur.AffineSpectrumKernelIdeal

/-!
# The prime-power subgroup is the repeated identity divisor

The Laurent orbit equation identifies the actual scheme ideal of roots of
unity with the power of the group identity's ideal. The statement holds over
any ring of characteristic p, with all infinitesimal multiplicities retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.RootsOfUnityPrimePowerIdeal

open MultiplicativeGroupScheme BaseAdicThickening

variable (R : Type*) [CommRing R]

/-- The Hopf counit is the Laurent evaluation at the identity unit. -/
theorem counit_eq_evalOne :
    Bialgebra.counitAlgHom R R[T;T⁻¹] = LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ) := by
  apply LaurentUnitPoints.hom_ext <;>
    simp only [Bialgebra.counitAlgHom_apply, LaurentPolynomial.counit_T,
      LaurentUnitPoints.evalUnit_T, one_zpow, Units.val_one]

/-- The actual identity section is the spectrum of Laurent evaluation at one. -/
theorem identity_left :
    η[gm R].left =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ))) := by
  rw [one_spec_asOver_spec_left, counit_eq_evalOne]

variable (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The full roots-of-unity subscheme is the prime-power identity thickening. -/
theorem ideal (r : ℕ) :
    RootsOfUnityCartier.ideal R (p ^ r) = (η[gm R].left.ker) ^ p ^ r := by
  rw [RootsOfUnityCartier.ideal, RootsOfUnityScheme.inclusion_left, identity_left,
    specMap_ker_baseIdeal, specMap_ker_baseIdeal]
  change baseIdeal (.of R[T;T⁻¹])
      (RingHom.ker (RootsOfUnityAlgebra.restriction R (p ^ r)).toAlgHom.toRingHom) =
    (baseIdeal (.of R[T;T⁻¹])
      (RingHom.ker (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom)) ^ p ^ r
  rw [RootsOfUnityPrimePowerOrbit.kernel, baseIdeal_pow]

/-- The scheme-theoretic orbit product consists of all repeated identity sections. -/
theorem ideal_product (r : ℕ) :
    RootsOfUnityCartier.ideal R (p ^ r) = ∏ _ : Fin (p ^ r), η[gm R].left.ker := by
  rw [ideal]
  simp

/-- The prime-power subgroup and identity section have exactly the same support. -/
theorem support (r : ℕ) :
    (RootsOfUnityCartier.ideal R (p ^ r)).support = η[gm R].left.ker.support := by
  rw [ideal, Scheme.IdealSheafData.support_pow _ _ (NeZero.ne (p ^ r))]

end FLT.Mazur.RootsOfUnityPrimePowerIdeal
