/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXStandardPuncture

/-!
# The full original Laurent map on the complete standard initial puncture

The entire original map factors through D(p), with its actual corrected
parameter. Restricting to the initial node neighborhood recovers every function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => R[T;T⁻¹]
local notation "L" => PolynomialNodeOpen W s
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "F" => polynomialNodeForwardBase W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3

local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- Evaluate the complete standard puncture using the full original Laurent boundary. -/
def laurentStandardPunctureEvaluation : D →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (NodalFiber.p s)
    (f := (G).comp (Algebra.algHom R N L))
    (laurentNodeRestriction_p_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
local notation "H" => laurentStandardPunctureEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- Every full node function has its original Laurent evaluation. -/
theorem laurentStandardPunctureEvaluation_base (z : N) :
    H (algebraMap N D z) = G (algebraMap N L z) := by
  rw [laurentStandardPunctureEvaluation, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The whole initial node restriction is recovered through the standard puncture. -/
theorem laurentStandardPunctureEvaluation_restriction :
    (H).comp (initialNodeStandardPuncture W s I hI ha hs) = G := by
  apply IsLocalization.algHom_ext (Submonoid.powers
    (NodalFiber.q s + algebraMap R N W.a₁))
  apply AlgHom.ext
  intro z
  change H (initialNodeStandardPuncture W s I hI ha hs (algebraMap N L z)) =
    G (algebraMap N L z)
  rw [initialNodeStandardPuncture_base, laurentStandardPunctureEvaluation_base]

/-- The standard first parameter retains the complete original opposite-factor correction. -/
theorem laurentStandardPunctureEvaluation_p :
    H (algebraMap N D (NodalFiber.p s)) =
      LaurentPolynomial.T (-1) * E false (polynomialOppositeFactor W s b3 b4 b6 r₀) := by
  rw [laurentStandardPunctureEvaluation_base, laurentNodeRestriction_p]

/-- The standard second parameter retains the complete original small factor. -/
theorem laurentStandardPunctureEvaluation_q :
    H (algebraMap N D (NodalFiber.q s)) =
      E false (polynomialSmallFactor W s b3 b4 b6 r₀) := by
  rw [laurentStandardPunctureEvaluation_base, laurentNodeRestriction_q]

end FLT.Mazur.WeierstrassModificationX
