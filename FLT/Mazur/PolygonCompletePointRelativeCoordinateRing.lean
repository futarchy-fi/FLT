/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointRelativeCoordinateSurjective
public import FLT.Mazur.WeierstrassAffineEvaluationInjective

/-!
# The relative contraction retains the entire complement function ring
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

local notation "W" => completePointWeierstrassCurve K n h i

/-- The original relative coordinate evaluation is injective over the actual base ring. -/
theorem completePointCoordinateEvaluation_injective :
    Function.Injective (completePointCoordinateEvaluation K n h i) :=
  WeierstrassAffineEquationEvaluation.evaluation_injective (W)
    (completePointComplementBaseMap K n h i) (completePointComplementX K n h i)
    (completePointComplementY K n h i) (completePointWeierstrass_equation K n h i)
    (completePointNormalMonomials_independent K n h i)

/-- The constructed relative cubic ring is the entire original complement function ring. -/
def completePointCoordinateRingEquiv : (W).toAffine.CoordinateRing ≃+*
    Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤) :=
  RingEquiv.ofBijective (completePointCoordinateEvaluation K n h i)
    ⟨completePointCoordinateEvaluation_injective K n h i,
      completePointCoordinateEvaluation_surjective K n h i⟩

/-- The original base ring map is retained by the constructed ring isomorphism. -/
theorem completePointCoordinateRingEquiv_scalar (a : Γ(S, ⊤)) :
    completePointCoordinateRingEquiv K n h i
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing a) =
        completePointComplementBaseMap K n h i a :=
  completePointCoordinateEvaluation_scalar K n h i a

/-- The ring isomorphism retains the original order-two function. -/
theorem completePointCoordinateRingEquiv_x :
    completePointCoordinateRingEquiv K n h i
      (algebraMap (Polynomial Γ(S, ⊤)) (W).toAffine.CoordinateRing Polynomial.X) =
        completePointComplementX K n h i :=
  completePointCoordinateEvaluation_x K n h i

/-- The ring isomorphism retains the original order-three function. -/
theorem completePointCoordinateRingEquiv_y :
    completePointCoordinateRingEquiv K n h i (AdjoinRoot.root (W).toAffine.polynomial) =
      completePointComplementY K n h i :=
  completePointCoordinateEvaluation_y K n h i


end FLT.Mazur.PolygonInfinitesimalStages
