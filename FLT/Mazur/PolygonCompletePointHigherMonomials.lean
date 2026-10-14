/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointComplementCoordinates

/-!
# Unit-leading monomial sections in every complete-base pole degree
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "e" => completePointSectionFrame K n h i

/-- Actual alternating x powers and x powers times y in the original H0 modules. -/
def completePointHigherMonomial : (m : ℕ) → ModuleRingH (f).appTop.hom
    (tensorPower (divisorLineBundle (s).ker hI) (m + 2)) 0
  | 0 => completePointPoleLift K n h i 0
  | 1 => completePointPoleLift K n h i 1
  | m + 2 => sectionPoleHZeroProduct f s hI (m + 2) 2
      (completePointHigherMonomial m) (completePointPoleLift K n h i 0)

/-- The initial higher monomial is the original order-two lift. -/
theorem completePointHigherMonomial_zero :
    completePointHigherMonomial K n h i 0 =
      completePointPoleLift K n h i 0 := rfl

/-- The next higher monomial is the original order-three lift. -/
theorem completePointHigherMonomial_one :
    completePointHigherMonomial K n h i 1 =
      completePointPoleLift K n h i 1 := rfl

/-- Increasing the order by two uses actual tensor-degree multiplication by x. -/
theorem completePointHigherMonomial_step (m : ℕ) :
    completePointHigherMonomial K n h i (m + 2) =
      sectionPoleHZeroProduct f s hI (m + 2) 2
        (completePointHigherMonomial K n h i m)
        (completePointPoleLift K n h i 0) := rfl

/-- Every constructed monomial has unit leading coefficient in the one original frame. -/
theorem completePointHigherMonomial_coefficient (m : ℕ) :
    completePointPoleCoefficient K n h i (m + 2)
      (completePointHigherMonomial K n h i m) = 1 := by
  induction m using Nat.twoStepInduction with
  | zero => exact completePointPoleLift_coefficient K n h i 0
  | one => exact completePointPoleLift_coefficient K n h i 1
  | more m ih _ =>
    exact (completePointPoleProduct_coefficient K n h i (m + 2) 2 _ _).trans
      ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b) ih
        (completePointPoleLift_coefficient K n h i 0)).trans (one_mul 1))

/-- The first function is x itself. -/
theorem completePointHigherMonomial_function_zero :
    relativePoleFunction f s hI 2 (completePointHigherMonomial K n h i 0) =
      completePointComplementX K n h i := rfl

/-- The second function is y itself. -/
theorem completePointHigherMonomial_function_one :
    relativePoleFunction f s hI 3 (completePointHigherMonomial K n h i 1) =
      completePointComplementY K n h i := rfl

/-- The actual functions satisfy multiplication by x at each two-degree step. -/
theorem completePointHigherMonomial_function_step (m : ℕ) :
    relativePoleFunction f s hI (m + 2 + 2)
      (completePointHigherMonomial K n h i (m + 2)) =
        relativePoleFunction f s hI (m + 2)
          (completePointHigherMonomial K n h i m) * completePointComplementX K n h i :=
  relativePoleFunction_product f s hI (m + 2) 2 _ _


end FLT.Mazur.PolygonInfinitesimalStages
