/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFiniteParameterLines
public import FLT.Mazur.PolygonCompleteMarkingLineTransition
public import FLT.Mazur.PolygonInfinitesimalDivisorLineSection

/-!
# Compatibility with the original finite boundary comparison

The parameter product comparison agrees with restricting to the original finite
stage and applying the existing Laurent coefficient comparison to its boundary line.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  tensorPowerPullbackComparison divisorLineBundle markingLineParameterIso
  PolygonInfinitesimal.scheme parameterProjection markingDivisor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => Over.hom (completeFiniteParameterOver K m)
local notation "e" => completeFiniteParameterProductIso K n h m
local notation "r" => scalingParameterProjection (A) (t) n h
local notation "p" => originalStageToCompatibleProj K n h m
local notation "c" => And.left
  (markingDivisor_cartier (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (fun _ ↦ 1))

local notation "Cₘ" => RingHom.toMonoidHom
  (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹])
local notation "cₘ" => And.left
  (markingDivisor_cartier (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h
    (fun _ ↦ Units.map (Cₘ) (1 : (A)ˣ)))

omit [NeZero n] in
/-- Coefficient transport of the unit-one markings retains their full original ideal. -/
theorem completeFiniteBoundaryCoefficientIdeal :
    markingDivisor (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h
      (fun _ ↦ Units.map (Cₘ) (1 : (A)ˣ)) =
        markingDivisor (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (fun _ ↦ 1) := by
  simp only [map_one]

/-- The existing Laurent comparison, with the canonical unit-one ideal identification. -/
def completeFiniteBoundaryCoefficientIso :
    (Scheme.Modules.pullback (r)).obj (boundaryLine K m n h) ≅
      markingLine (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (fun _ ↦ 1) :=
  markingLineParameterIso (t) n h LaurentPolynomial.C (LaurentPolynomial.C (t))
    rfl (fun _ ↦ (1 : (A)ˣ)) ≪≫
      divisorLineBundleEqIso (completeFiniteBoundaryCoefficientIdeal K n h m) (cₘ) (c)

omit [NeZero n] in
/-- The existing coefficient comparison preserves the finite boundary section. -/
theorem completeFiniteBoundaryCoefficientIso_section :
    DivisorLineSectionCompatible (r) (boundaryIdeal_cartier K m n h).1 (c)
      (completeFiniteBoundaryCoefficientIso K n h m) :=
  (markingLineParameterIso_section (t) n h LaurentPolynomial.C
    (LaurentPolynomial.C (t)) rfl (fun _ ↦ (1 : (A)ˣ))).targetIdealEq
      (completeFiniteBoundaryCoefficientIdeal K n h m)

/-- The parameter product comparison agrees exactly with the original stage boundary path. -/
theorem completeFiniteBoundaryLine_square :
    LinePullbackSquare (e).hom (pullback.fst (exactVeroneseProjToBase K n h) (s)) (r) (p)
      (completeFiniteParameterProductIso_fst K n h m)
      (completeMarkingLineBaseChangeIso K n h (s)) (completeFiniteParameterLineIso K n h m)
      (completeMarkingLineStageIso K n h m) (completeFiniteBoundaryCoefficientIso K n h m) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeMarkingLineBaseChangeIso_section K n h (s))
    (completeFiniteParameterLineIso_section K n h m)
    (completeMarkingLineStageIso_section K n h m)
    (completeFiniteBoundaryCoefficientIso_section K n h m)

/-- The same old boundary comparison agrees in every tensor degree. -/
theorem completeFiniteBoundaryLine_power_square (d : ℕ) :
    LinePullbackSquare (e).hom (pullback.fst (exactVeroneseProjToBase K n h) (s)) (r) (p)
      (completeFiniteParameterProductIso_fst K n h m)
      (tensorPowerPullbackComparison _ (completeMarkingLineBaseChangeIso K n h (s)) d)
      (tensorPowerPullbackComparison _ (completeFiniteParameterLineIso K n h m) d)
      (tensorPowerPullbackComparison _ (completeMarkingLineStageIso K n h m) d)
      (tensorPowerPullbackComparison _ (completeFiniteBoundaryCoefficientIso K n h m) d) :=
  (completeFiniteBoundaryLine_square K n h m).tensorPower d

end FLT.Mazur.PolygonInfinitesimalStages
