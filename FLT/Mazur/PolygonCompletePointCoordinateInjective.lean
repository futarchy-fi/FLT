/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredPoleInfiniteIndependence
public import FLT.Mazur.PolygonCompletePointAffineMorphism
public import FLT.Mazur.WeierstrassAffineEvaluationInjective
public import FLT.Mazur.WeightedPoleNormalForms

/-!
# Faithful coordinates on the original marked-point complement

Exact pole orders imply independence of all original monomials, including
those after normalization. The actual affine coordinate evaluation is
therefore injective. No exhaustion or affineness hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- All original ordered monomials are independent for the actual base-field action. -/
theorem completeCartesianPointMonomial_linearIndependent (i : Fin n) :
    let _ := Module.compHom
      Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)
      (completeCartesianPointScalar K n h L s p q hs i)
    LinearIndependent L (completeCartesianPointMonomial K n h L s p q hs i) :=
  FilteredPoleBasis.linearIndependent_of_nat_orders
    (divisorPoleSubmodule q (completeCartesianMarking_relativeCartier K n h s p q hs i).1)
    (divisorPoleSubmodule_mono q _) _ _ WeightedPoleMonomials.order_strictMono
    (completeCartesianPointMonomial_mem K n h L s p q hs i)
    (completeCartesianPointMonomial_ne_zero K n h L s p q hs i)
    (completeCartesianPointMonomial_not_mem_lt K n h L s p q hs i)

/-- The normalized ordered monomials remain independent in the original function ring. -/
theorem completeCartesianPointNormalizedMonomial_linearIndependent (i : Fin n) :
    let _ := Module.compHom
      Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)
      (completeCartesianPointScalar K n h L s p q hs i)
    LinearIndependent L (WeightedPoleMonomials.monomial
      (completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)))
      (completeCartesianPointNormalize K n h L s p q hs i
        (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)))) :=
  WeightedPoleMonomials.linearIndependent_scaled
    (completeCartesianPointScalar K n h L s p q hs i) _ _ _
    (completeCartesianPointCubicCoefficients_last_ne_zero K n h L s p q hs i)
    (completeCartesianPointMonomial_linearIndependent K n h L s p q hs i)

/-- The original affine coordinate evaluation has trivial kernel. -/
theorem completeCartesianPointCoordinateEvaluation_injective (i : Fin n) :
    Function.Injective (completeCartesianPointCoordinateEvaluation K n h L s p q hs i) := by
  apply WeierstrassAffineEquationEvaluation.evaluation_injective
  let _ := Module.compHom
    Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)
    (completeCartesianPointScalar K n h L s p q hs i)
  exact WeightedPoleMonomials.linearIndependent_normal _ _
    (completeCartesianPointNormalizedMonomial_linearIndependent K n h L s p q hs i)

end FLT.Mazur.PolygonInfinitesimalStages
