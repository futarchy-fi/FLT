/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointComplementEquation
public import FLT.Mazur.WeierstrassAffineEquationEvaluation

/-!
# The original complete-base affine coordinate evaluation
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

local notation "x" => completePointComplementX K n h i
local notation "y" => completePointComplementY K n h i
local notation "φ" => completePointComplementBaseMap K n h i
local notation "W" => completePointWeierstrassCurve K n h i

/-- Evaluate the constructed affine coordinate ring in the original complement functions. -/
def completePointCoordinateEvaluation : (W).toAffine.CoordinateRing →+*
    Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤) :=
  WeierstrassAffineEquationEvaluation.evaluation W φ x y
    (completePointWeierstrass_equation K n h i)

/-- Evaluation retains the original coefficient map. -/
theorem completePointCoordinateEvaluation_scalar (r : Γ(S, ⊤)) :
    completePointCoordinateEvaluation K n h i
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing r) = φ r :=
  WeierstrassAffineEquationEvaluation.evaluation_scalar W φ x y _ r

/-- The coordinate-ring map is over the actual base ring. -/
theorem completePointCoordinateEvaluation_comp_scalar :
    (completePointCoordinateEvaluation K n h i).comp
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing) = φ :=
  RingHom.ext (completePointCoordinateEvaluation_scalar K n h i)

/-- The first universal coordinate evaluates to the original order-two function. -/
theorem completePointCoordinateEvaluation_x :
    completePointCoordinateEvaluation K n h i
      (algebraMap (Polynomial Γ(S, ⊤)) (W).toAffine.CoordinateRing Polynomial.X) = x :=
  WeierstrassAffineEquationEvaluation.evaluation_x W φ x y _

/-- The second universal coordinate evaluates to the original order-three function. -/
theorem completePointCoordinateEvaluation_y :
    completePointCoordinateEvaluation K n h i (AdjoinRoot.root (W).toAffine.polynomial) = y :=
  WeierstrassAffineEquationEvaluation.evaluation_y W φ x y _

/-- The actual scheme morphism defined by the original normalized pole functions. -/
def completePointToAffineCubic :
    Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl ⟶
      Spec (.of (W).toAffine.CoordinateRing) :=
  (Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (completePointCoordinateEvaluation K n h i))

/-- The scheme morphism has the original structure map to the affine base spectrum. -/
theorem completePointToAffineCubic_over :
    completePointToAffineCubic K n h i ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := exactVeroneseProj K n h) (s).ker.support.compl) ≫
          f ≫ (S).toSpecΓ := by
  rw [completePointToAffineCubic, Category.assoc, ← Spec.map_comp]
  change (Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((completePointCoordinateEvaluation K n h i).comp
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing))) = _
  rw [completePointCoordinateEvaluation_comp_scalar]
  change _ ≫ Spec.map ((f).appTop ≫
    (Scheme.Opens.ι (X := exactVeroneseProj K n h) (s).ker.support.compl).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← Scheme.toSpecΓ_naturality]


end FLT.Mazur.PolygonInfinitesimalStages
