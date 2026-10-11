/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedPointQuotient

/-!
# Coefficients in actual affine closed-point neighborhoods

The germ-induced quotient comparison is an algebra equivalence for any
coefficient map to the affine sections. The stalk coefficients are the
composite with the actual germ, so no identification of stalks is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineClosedPointQuotient

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] {X : Scheme}
  (U : X.affineOpens) (x : U.1) (hx : IsClosed {(x : X)})
  (s : R →+* Γ(X, U))

/-- The original coefficients in the actual stalk, through the original germ. -/
def stalkScalars : R →+* X.presheaf.stalk x :=
  (X.presheaf.germ U x x.2).hom.comp s

/-- The germ comparison at every ideal power preserves the specified coefficients. -/
def algebraEquivalence (r : ℕ) :
    let _ := s.toAlgebra
    let _ := (stalkScalars U x s).toAlgebra
    (Γ(X, U) ⧸ (U.2.primeIdealOf x).asIdeal ^ r) ≃ₐ[R]
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ r) := by
  let _ := s.toAlgebra
  let _ := (stalkScalars U x s).toAlgebra
  refine { equivalence U x hx r with commutes' := ?_ }
  intro a
  exact equivalence_mk U x hx r (s a)

/-- The algebra comparison still sends a section to its actual germ. -/
@[simp] theorem algebraEquivalence_mk (r : ℕ) (a : Γ(X, U)) :
    algebraEquivalence U x hx s r (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (X.presheaf.germ U x x.2 a) :=
  equivalence_mk U x hx r a

/-- All ideal-power transitions commute with the coefficient-preserving comparison. -/
theorem algebraEquivalence_transition {a b : ℕ} (hab : a ≤ b)
    (t : Γ(X, U) ⧸ (U.2.primeIdealOf x).asIdeal ^ b) :
    let _ := s.toAlgebra
    let _ := (stalkScalars U x s).toAlgebra
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hab)
        (algebraEquivalence U x hx s b t) =
      algebraEquivalence U x hx s a
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hab) t) :=
  equivalence_transition U x hx hab t

end FLT.Mazur.AffineClosedPointQuotient
