/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCyclicPresentation
public import FLT.GroupScheme.RaynaudFiniteCoordinateGeneration

/-!
# Derived cyclic presentations of actual finite-flat models

Both the coefficients and the presentation isomorphism are constructed
from the scalar action and rank-one generic point space. The polynomial
variables are sent to the previously constructed integral coordinates.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

/-- Successor in a nonempty Frobenius cycle. -/
def cycleNext (r : ℕ+) (i : Fin r) : Fin r := ⟨(i.val + 1) % r, Nat.mod_lt _ r.pos⟩

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)
  (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))

/-- Choose the already proved integral cyclic coefficients. -/
def FF.fundamentalCoefficient : Fin r → R :=
  (X.exists_finite_fundamental_relations lift h1 hmul p hdim hlift e r hr).choose

omit [Invertible (Fintype.card Fˣ : R)] in
/-- The chosen coefficients satisfy the actual cyclic coordinate equations. -/
theorem FF.fundamentalCoefficient_spec (i : Fin r) :
    X.fundamentalCoordinate p lift h1 hmul hdim hlift e i ^ p =
      X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i •
        X.fundamentalCoordinate p lift h1 hmul hdim hlift e (cycleNext r i) :=
  (X.exists_finite_fundamental_relations lift h1 hmul p hdim hlift e r hr).choose_spec i

/-- The actual model is the quotient by its derived cyclic power relations. -/
def FF.fundamentalPresentation :
    (MvPolynomial (Fin r) R ⧸ CyclicPresentation.relations p (cycleNext r)
      (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr)) ≃ₐ[R] X.CoordinateRing := by
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  exact CyclicPresentation.equiv p (cycleNext r)
    (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr)
    (fun i : Fin r ↦ X.fundamentalCoordinate p lift h1 hmul hdim hlift e i)
    (X.fundamentalCoefficient_spec lift h1 hmul p hdim hlift e r hr)
    (CharP.char_is_prime F p).one_lt
    (X.fundamental_aeval_surjective lift h0 h1 hmul hadd p hdim hlift e r hr)
    (by simpa using X.fundamental_coordinate_finrank p hdim r hr)

/-- The presentation identifies each quotient variable with the actual integral coordinate. -/
theorem FF.fundamentalPresentation_coordinate (i : Fin r) :
    X.fundamentalPresentation lift h0 h1 hmul hadd p hdim hlift e r hr
      (CyclicPresentation.coordinate p (cycleNext r)
        (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr) i) =
      X.fundamentalCoordinate p lift h1 hmul hdim hlift e i := by
  change MvPolynomial.aeval
    (fun j : Fin r ↦ X.fundamentalCoordinate p lift h1 hmul hdim hlift e j)
    (MvPolynomial.X i) = _
  simp

end ThreeAdicPlan
