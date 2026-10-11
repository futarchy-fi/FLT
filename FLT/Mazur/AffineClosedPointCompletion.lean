/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionQuotientEquiv
public import FLT.Mazur.AffineClosedPointAlgebra

/-!
# Completion of an actual affine closed-point stalk

The compatible germ-induced algebra equivalences identify the completion of
affine sections at a closed point with the completion of the actual stalk.
The comparison preserves the original coefficients and the original germs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineClosedPointQuotient

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] {X : Scheme}
  (U : X.affineOpens) (x : U.1) (hx : IsClosed {(x : X)})
  (s : R →+* Γ(X, U))

/-- Completion of sections at the actual closed point agrees with its completed stalk. -/
def completionAlgebraEquivalence :
    let _ := s.toAlgebra
    let _ := (stalkScalars U x s).toAlgebra
    AdicCompletion (U.2.primeIdealOf x).asIdeal Γ(X, U) ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) := by
  let _ := s.toAlgebra
  let _ := (stalkScalars U x s).toAlgebra
  exact AdicCompletionQuotientEquiv.equivalence _ _ (algebraEquivalence U x hx s)
    (algebraEquivalence_transition U x hx s)

/-- Every evaluation of the completed comparison is the actual germ quotient map. -/
theorem completionAlgebraEquivalence_eval (r : ℕ)
    (a : AdicCompletion (U.2.primeIdealOf x).asIdeal Γ(X, U)) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) r
        (completionAlgebraEquivalence U x hx s a) =
      algebraEquivalence U x hx s r
        (AdicCompletion.evalₐ (U.2.primeIdealOf x).asIdeal r a) := by
  let _ := s.toAlgebra
  let _ := (stalkScalars U x s).toAlgebra
  exact AdicCompletionQuotientEquiv.eval_map _ _ (algebraEquivalence U x hx s)
    (algebraEquivalence_transition U x hx s) r a

/-- The completed comparison extends the original germ on every affine section. -/
@[simp] theorem completionAlgebraEquivalence_of (a : Γ(X, U)) :
    completionAlgebraEquivalence U x hx s
        (AdicCompletion.of (U.2.primeIdealOf x).asIdeal Γ(X, U) a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) (X.presheaf.germ U x x.2 a) := by
  apply AdicCompletion.ext_evalₐ
  intro r
  rw [completionAlgebraEquivalence_eval, AdicCompletion.evalₐ_of,
    AdicCompletion.evalₐ_of, algebraEquivalence_mk]

end FLT.Mazur.AffineClosedPointQuotient
