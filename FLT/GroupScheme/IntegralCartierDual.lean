/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualEtale
public import FLT.GroupScheme.DiagonalizableFiniteFlat
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Integral Cartier duals over the integers with two inverted

Finite flat coordinate algebras over a principal ideal domain are finite
free. Their integral dual Hopf algebras have étale rational generic fibres,
so they define finite-flat objects with their full geometric point groups.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- Localizing the integers at two preserves principality of all ideals. -/
instance zInvTwoPrincipalIdealRing : IsPrincipalIdealRing ZInvTwo where
  principal I := by
    rw [← IsLocalization.map_under (Submonoid.powers (2 : ℤ)) ZInvTwo I]
    exact Submodule.IsPrincipal.map_ringHom _ (inferInstance : (I.under ℤ).IsPrincipal)

/-- The Cartier dual finite-flat object, using the integral linear dual of
its chosen coordinate Hopf algebra and the actual geometric generic points. -/
def FiniteFlatObject.cartierDual {R : Type} [CommRing R] [Algebra R ℚ]
    [IsDomain R] [IsPrincipalIdealRing R] (H : FiniteFlatObject R) : FiniteFlatObject R := by
  let D := HopfAlgebra.CartierDual R H.model.CoordinateRing
  let : Algebra.Etale ℚ (HopfAlgebra.CartierDual ℚ (ℚ ⊗[R] H.model.CoordinateRing)) :=
    HopfAlgebra.CartierDual.etale ℚ (ℚ ⊗[R] H.model.CoordinateRing)
  let : Algebra.Etale ℚ (ℚ ⊗[R] D) :=
    Algebra.Etale.of_equiv (HopfAlgebra.CartierDual.baseChangeAlgEquiv ℚ).symm
  exact FiniteFlatObject.ofCoordinateRing D

/-- The integral dual coordinate algebra of a diagonalizable group is the
function algebra of its finite character group. -/
def diagonalizableDualCoordinateEquiv (A : Type) [AddCommGroup A] [Finite A] :
    (diagonalizableFiniteFlat A).cartierDual.model.CoordinateRing ≃ₐ[ZInvTwo]
      (Multiplicative A → ZInvTwo) :=
  HopfAlgebra.CartierDual.groupAlgebraEquiv ZInvTwo (Multiplicative A)

/-- The integral Cartier dual of a finite diagonalizable group is étale. -/
theorem diagonalizable_cartierDual_etale (A : Type) [AddCommGroup A] [Finite A] :
    Algebra.Etale ZInvTwo (diagonalizableFiniteFlat A).cartierDual.model.CoordinateRing :=
  Algebra.Etale.of_equiv (diagonalizableDualCoordinateEquiv A).symm

/-- The integral dual of the cube-root group has the constant three-point
function algebra, without inverting three. -/
def muThreeDualCoordinateEquiv :
    muThree.cartierDual.model.CoordinateRing ≃ₐ[ZInvTwo]
      (Multiplicative (ZMod 3) → ZInvTwo) :=
  diagonalizableDualCoordinateEquiv (ZMod 3)

/-- The integral dual of the cube-root group is étale over `ℤ[1/2]`. -/
theorem muThree_cartierDual_etale :
    Algebra.Etale ZInvTwo muThree.cartierDual.model.CoordinateRing :=
  diagonalizable_cartierDual_etale (ZMod 3)

end ThreeAdicPlan
