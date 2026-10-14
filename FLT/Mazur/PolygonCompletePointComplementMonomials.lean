/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointComplementCoordinates
public import FLT.Mazur.PolygonCompletePointIntegralMonomials

/-!
# Integral monomial bases as actual complement functions

Every original basis vector through degree six represents the expected monomial.
The old vectors retain the original canonical divisor inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

/-- The first three ordered monomials, indexed like the original low-pole basis. -/
def completePointLowMonomial {R : Type*} [CommRing R] (x y : R) :
    ((Unit ⊕ Unit) ⊕ Unit) → R :=
  Sum.elim (Sum.elim (fun _ ↦ 1) (fun _ ↦ x)) (fun _ ↦ y)

/-- The five lower monomials in the original cubic coefficient order. -/
def completePointLowerMonomial {R : Type*} [CommRing R] (x y : R) :
    ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → R :=
  Sum.elim (Sum.elim (completePointLowMonomial x y) (fun _ ↦ x ^ 2)) (fun _ ↦ x * y)

/-- The retained first three basis vectors represent exactly 1, x and y. -/
theorem completePointComplement_threeBasis (j : (Unit ⊕ Unit) ⊕ Unit) :
    relativePoleFunction f s hI 3 (completePointThreeCanonicalBasis K n h i j) =
      completePointLowMonomial (completePointComplementX K n h i)
        (completePointComplementY K n h i) j := by
  rcases j with ((u | u) | u) <;> cases u
  · rw [completePointThreeCanonicalBasis_one, relativePoleFunction_step,
      relativePoleFunction_step, completePointComplement_oneBasis]
    rfl
  · rw [completePointThreeCanonicalBasis_x, relativePoleFunction_step]
    rfl
  · rw [completePointThreeCanonicalBasis_new]
    rfl

/-- The fourth basis vector adds the square of the actual x function. -/
theorem completePointComplement_fourBasis (j : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction f s hI 4 (completePointFourMonomialBasis K n h i j) =
      Sum.elim (completePointLowMonomial (completePointComplementX K n h i)
        (completePointComplementY K n h i))
        (fun _ ↦ completePointComplementX K n h i ^ 2) j := by
  rcases j with i | u
  · rw [completePointFourMonomialBasis_old, relativePoleFunction_step,
      completePointComplement_threeBasis]
    rfl
  · cases u
    rw [completePointFourMonomialBasis_new, completePointComplement_square]
    rfl

/-- The original order-five basis represents exactly the five lower monomials. -/
theorem completePointComplement_fiveBasis (j : (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction f s hI 5 (completePointFiveMonomialBasis K n h i j) =
      completePointLowerMonomial (completePointComplementX K n h i)
        (completePointComplementY K n h i) j := by
  rcases j with i | u
  · rw [completePointFiveMonomialBasis_old, relativePoleFunction_step,
      completePointComplement_fourBasis]
    rfl
  · cases u
    rw [completePointFiveMonomialBasis_new, completePointComplement_mixed]
    rfl

/-- All six actual order-six basis functions are the expected monomials. -/
theorem completePointComplement_sixBasis
    (j : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction f s hI 6 (completePointSixMonomialBasis K n h i j) =
      Sum.elim (completePointLowerMonomial (completePointComplementX K n h i)
        (completePointComplementY K n h i))
        (fun _ ↦ completePointComplementX K n h i ^ 3) j := by
  rcases j with i | u
  · rw [completePointSixMonomialBasis_old, relativePoleFunction_step,
      completePointComplement_fiveBasis]
    rfl
  · cases u
    rw [completePointSixMonomialBasis_new, completePointComplement_cube]
    rfl

end FLT.Mazur.PolygonInfinitesimalStages
