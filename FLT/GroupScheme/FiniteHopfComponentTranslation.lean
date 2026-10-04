/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraComponentMap
public import FLT.GroupScheme.FiniteAlgebraComponentPoint
public import FLT.GroupScheme.FiniteHopfIdentityComponent
public import FLT.GroupScheme.HopfPointTranslation

/-! # Translation identifies each local factor with the identity factor -/

@[expose] public noncomputable section

namespace HopfAlgebra

open FiniteAlgebra

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsArtinianRing A] [Module.Finite k A]

/-- Translation restricts to the factor at the chosen point and the identity factor. -/
def pointComponentTranslation (χ : A →ₐ[k] k) :
    PointComponent χ ≃ₐ[k] FiniteIdentityComponent k A :=
  pointComponentEquiv χ (Bialgebra.counitAlgHom k A) (pointTranslation χ)
    (counit_comp_pointTranslation χ)

omit [Module.Finite k A] in
/-- The restricted translation retains the original coordinate comultiplication. -/
theorem pointComponentTranslation_projection (χ : A →ₐ[k] k) (a : A) :
    pointComponentTranslation χ (pointProjection χ a) = finiteIdentityProjection k A
      (Algebra.TensorProduct.lid k A
        (Algebra.TensorProduct.map χ (AlgHom.id k A) (Coalgebra.comul (R := k) a))) := by
  change finiteIdentityProjection k A (pointTranslation χ a) = _
  rw [pointTranslation_apply]

/-- Every geometric local factor is isomorphic to the identity Hopf factor. -/
theorem nonempty_componentEquiv_identity [IsAlgClosed k] (m : ComponentIndex A) :
    Nonempty (Component A m ≃ₐ[k] FiniteIdentityComponent k A) := by
  obtain ⟨χ, hχ⟩ := exists_pointComponentIndex_eq (k := k) m
  have hI : pointComponentIdeal χ = Ideal.span {1 - componentIdempotent A m} := by
    rw [pointComponentIdeal, hχ]
  exact ⟨(Ideal.quotientEquivAlgOfEq k hI).symm.trans (pointComponentTranslation χ)⟩

end HopfAlgebra
