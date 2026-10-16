/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstFourCoordinates
public import FLT.Mazur.PolygonCompleteIdentityFirstPolynomialErrors

/-!
# Convert original four-coordinate polynomials to target-coordinate polynomials

The source coordinates become coefficients in the unchanged source node ring.
This conversion commutes with both the actual ambient presentation and the
reciprocal-scaled source substitution; it retains all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1

/-- Group the original source variables into coefficients, keeping the target variables. -/
def completeIdentityFirstPolynomialConversion :
    MvPolynomial (Fin 2 ⊕ Fin 2) (S) →+* MvPolynomial (Fin 2) (ChartRing (e)) :=
  (MvPolynomial.map (Ideal.Quotient.mk (relationIdeal (e)))).comp
    (MvPolynomial.sumRingEquiv (S) (Fin 2) (Fin 2)).toRingHom
local notation "C" => completeIdentityFirstPolynomialConversion K

/-- The original four-coordinate map factors through this literal conversion. -/
theorem completeIdentityFirstPolynomialConversion_map
    (n : ℕ) (h : 2 ≤ n) [NeZero n] (p : MvPolynomial (Fin 2 ⊕ Fin 2) (S)) :
    completeIdentityFirstNodePolynomialMap K n h ((C) p) =
      completeIdentityFirstFourCoordinateMap K n h p := rfl

/-- Every target-coordinate polynomial has an original four-coordinate representative. -/
theorem completeIdentityFirstPolynomialConversion_surjective : Function.Surjective (C) :=
  (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp
    (MvPolynomial.sumRingEquiv (S) (Fin 2) (Fin 2)).surjective

/-- Target variables survive unchanged. -/
theorem completeIdentityFirstPolynomialConversion_target (j : Fin 2) :
    (C) (MvPolynomial.X (.inl j)) = MvPolynomial.X j := by
  simp [completeIdentityFirstPolynomialConversion]

/-- Source variables become their original node-ring coefficients. -/
theorem completeIdentityFirstPolynomialConversion_source (j : Fin 2) :
    (C) (MvPolynomial.X (.inr j)) =
      MvPolynomial.C (Ideal.Quotient.mk (relationIdeal (e)) (MvPolynomial.X j)) := by
  simp [completeIdentityFirstPolynomialConversion]

end FLT.Mazur.PolygonInfinitesimalStages
