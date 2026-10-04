/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierPairing
public import FLT.GroupScheme.IntegralCartierPoints

/-! # Perfect character duality on the original local point groups -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
open HopfAlgebra.CartierDual
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  (X : FF R K)

/-- Every character of the original geometric points is a unique actual dual point. -/
def FF.cartierCharactersEquiv :
    X.cartierDual.Points ≃+ Additive (Multiplicative X.Points →* (AlgebraicClosure K)ˣ) :=
  X.cartierDual.pointsEquiv.symm.trans
    ((precompPointsEquiv (AlgebraicClosure K) X.cartierDualGenericEquiv.symm).trans
      ((geometricCharactersMulEquiv K (AlgebraicClosure K)
        (K ⊗[R] X.CoordinateRing)).toAdditive.trans
          (characterSourceEquiv X.pointsEquiv.toMultiplicativeRight.symm).toAdditive))

/-- The perfect character comparison uses the original finite Cartier evaluation. -/
@[simp] theorem FF.cartierCharactersEquiv_apply (y : X.cartierDual.Points) (x : X.Points) :
    (X.cartierCharactersEquiv y).toMul (Multiplicative.ofAdd x) = X.cartierPairing y x := rfl

/-- The actual pairing is additive in the dual argument. -/
theorem FF.cartierPairing_add_left (y z : X.cartierDual.Points) (x : X.Points) :
    X.cartierPairing (y + z) x = X.cartierPairing y x * X.cartierPairing z x :=
  congrArg (fun c ↦ c.toMul (Multiplicative.ofAdd x)) (X.cartierCharactersEquiv.map_add y z)

/-- Finite Cartier evaluation separates the full original dual point group. -/
theorem FF.cartierPairing_separates_dual {y z : X.cartierDual.Points}
    (h : ∀ x : X.Points, X.cartierPairing y x = X.cartierPairing z x) : y = z := by
  apply X.cartierCharactersEquiv.injective
  apply Additive.toMul.injective
  apply MonoidHom.ext
  intro x
  exact h x.toAdd

end ThreeAdicPlan
