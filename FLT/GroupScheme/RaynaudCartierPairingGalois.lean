/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierPairing

/-! # Original local Galois equivariance of Cartier evaluation -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  (X : FF R K) (σ : Field.absoluteGaloisGroup K)

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K] in
/-- Recovering geometric coordinates respects the original Galois action. -/
theorem FF.pointCoordinate_smul (x : X.Points) :
    X.pointCoordinate (σ • x) = σ • X.pointCoordinate x :=
  congrArg Additive.toMul (map_smul X.inversePoints σ x)

/-- Dual generic coordinate evaluation respects that same local Galois action. -/
theorem FF.dualPointCoordinate_smul (y : X.cartierDual.Points) :
    X.dualPointCoordinate (σ • y) = σ • X.dualPointCoordinate y := by
  unfold FF.dualPointCoordinate
  rw [X.cartierDual.pointCoordinate_smul]
  rfl

/-- Simultaneous Galois conjugation acts on the actual Cartier value. -/
theorem FF.cartierPairing_smul (y : X.cartierDual.Points) (x : X.Points) :
    X.cartierPairing (σ • y) (σ • x) = σ • X.cartierPairing y x := by
  unfold FF.cartierPairing
  rw [X.dualPointCoordinate_smul, X.pointCoordinate_smul,
    HopfAlgebra.CartierDual.geometricCharactersEquiv_smul, inv_smul_smul]

end ThreeAdicPlan
