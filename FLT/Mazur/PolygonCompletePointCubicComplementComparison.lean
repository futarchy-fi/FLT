/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointComplementCubicChart
public import FLT.Mazur.PolygonCompletePointNodeCubicChart

/-!
# A cubic comparison supplies the actual full target marking complement

A target with the same contracted cubic as a localized source lands in the
entire marking complement. Chart monomorphy identifies both original poles
without localizing either target coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "a" => PolygonInfinitesimal.chart (A) (t) n h j
local notation "r" => originalStageToCompatibleProj K n h m
local notation "g" => completePointToIntegralCubic K n h i
local notation "E" => completePointWeierstrassCurve K n h i
local notation "N" => completePointStageNodeOpen K n h m i j
local notation "d" => completePointNodeToCubicChart K n h m i j
variable {B : Type} [CommRing B] (σ : ChartRing (parameter K m) →+* B)
variable (β : StageNodeLocalization K m →+* B)
variable (he : Spec.map (CommRingCat.ofHom β) ≫ completePointNodeToCubicChart K n h m i j ≫
  integralCurveChart (completePointWeierstrassCurve K n h i) 2 =
    Spec.map (CommRingCat.ofHom σ) ≫ PolygonInfinitesimal.chart (Ring K m) (parameter K m) n h j ≫
      originalStageToCompatibleProj K n h m ≫ completePointToIntegralCubic K n h i)

include he

/-- Cubic equality places the actual target in the full original marking complement. -/
theorem completePointCubicComparison_target_range :
    Set.range (Spec.map (CommRingCat.ofHom σ)) ⊆ Set.range (N).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  have hz : (Spec.map (CommRingCat.ofHom σ) ≫ (a) ≫ (r) ≫ (g)) z ∈
      (integralCurveChart (E) 2).opensRange := by
    rw [← he]
    exact ⟨(Spec.map (CommRingCat.ofHom β) ≫ (d)) z, rfl⟩
  change Spec.map (CommRingCat.ofHom σ) z ∈
    ((a) ≫ (r) ≫ (g)) ⁻¹ᵁ (integralCurveChart (E) 2).opensRange at hz
  have hp : ((a) ≫ (r) ≫ (g)) ⁻¹ᵁ (integralCurveChart (E) 2).opensRange = (N) := by
    simp only [Scheme.Hom.comp_preimage, completePointToIntegralCubic_preimage_chart]
    rw [completePointStageNodeOpen, completePointStageComplement_preimage]
    rfl
  exact hp ▸ hz

/-- The comparison constructs the target factorization without inverting a target denominator. -/
def completePointCubicComparisonTargetComplement : Spec (.of B) ⟶ (N).toScheme :=
  IsOpenImmersion.lift (N).ι (Spec.map (CommRingCat.ofHom σ))
    (completePointCubicComparison_target_range K n h m i j σ β he)
local notation "q" => completePointCubicComparisonTargetComplement K n h m i j σ β he

/-- The factorization retains the entire original target morphism. -/
@[reassoc] theorem completePointCubicComparisonTargetComplement_inclusion :
    (q) ≫ (N).ι = Spec.map (CommRingCat.ofHom σ) := IsOpenImmersion.lift_fac _ _ _

/-- Monomorphy of the actual cubic chart identifies the two affine cubic maps. -/
theorem completePointCubicComparison_chart :
    Spec.map (CommRingCat.ofHom β) ≫ (d) =
      (q) ≫ completePointStageComplementToCubicChart K n h m i j := by
  apply (cancel_mono (integralCurveChart (E) 2)).mp
  simp only [Category.assoc, completePointStageComplementToCubicChart_inclusion,
    completePointCubicComparisonTargetComplement_inclusion_assoc]
  exact he

local notation "ψ" => completePointNodeComplementFunctions K n h m i j (q)

/-- Every original cubic function has identical source and target pullbacks. -/
theorem completePointCubicComparison_functions (z : Coordinate (E) 2) :
    β (completePointNodeCubicFunctions K n h m i j z) =
      (ψ) (completePointStageComplementCubicFunctions K n h m i j z) := by
  have hh := congrArg (fun w ↦ (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv ≫
    w.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom)
      (completePointCubicComparison_chart K n h m i j σ β he)
  simp only [Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality] at hh
  exact congrArg (fun w : CommRingCat.of (Coordinate (E) 2) ⟶ CommRingCat.of B ↦ w z) hh

/-- Both retained poles agree on the full target complement. -/
theorem completePointCubicComparison_poles :
    β (completePointNodeLocalizedPoleTwo K n h m i j) =
        (ψ) (completePointStageNodePoleTwo K n h m i j) ∧
      β (completePointNodeLocalizedPoleThree K n h m i j) =
        (ψ) (completePointStageNodePoleThree K n h m i j) := by
  constructor
  · simpa only [completePointNodeCubicFunctions_coordinate,
      completePointStageComplementCubicFunctions_coordinate, completePointStageNodeCubic_X,
      Matrix.cons_val_zero] using
      completePointCubicComparison_functions K n h m i j σ β he (coord (E) 2 0)
  · simpa only [completePointNodeCubicFunctions_coordinate,
      completePointStageComplementCubicFunctions_coordinate, completePointStageNodeCubic_Y,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      completePointCubicComparison_functions K n h m i j σ β he (coord (E) 2 1)

end FLT.Mazur.PolygonInfinitesimalStages
