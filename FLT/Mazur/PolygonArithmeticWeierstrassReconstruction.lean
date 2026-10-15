/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticClosedTargetReconstruction
public import FLT.Mazur.PolygonArithmeticProjectiveReconstruction
public import FLT.Mazur.WeierstrassIntegralProjectiveClosed
public import FLT.Mazur.PolygonArithmeticMarkingUniqueness

/-!
# Algebraizing original arithmetic maps to a specified Weierstrass cubic

Compatible coordinate sections first give a global projective morphism. Actual
maps from every original arithmetic stage into the specified integral cubic
then force its global factorization. The original coefficient and stage maps
are retained. Constructing those finite-stage maps is a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase completeOriginalProjectiveMap
  integralCurve integralProjectiveMap
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)
  (s : Fin 3 → ∀ m, Γ(completeLineOnStage A π hne hgen n h L m, ⊤))
  (hs : ∀ i a b (hab : a ≤ b),
    (completeLineStageTransitionIso A π hne hgen n h L (homOfLE hab)).hom.app ⊤
      (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s i b)) = s i a)
  (hcover : (⨆ i, sectionGeneratorOpen
    (completeLineOnStage A π hne hgen n h L 0) (s i 0)) = ⊤)
  (W : WeierstrassCurve A) (g : ∀ m, (family A π m n h).left ⟶ integralCurve W)
  (hg : ∀ m, g m ≫ integralProjectiveMap W =
    originalStageToCompatibleProj A π hne hgen n h m ≫
      completeOriginalProjectiveMap A π hne hgen n h L hL 2 s hs hcover)

include hg in
/-- Specified original-stage cubic maps give a unique actual complete arithmetic cubic map. -/
theorem completeWeierstrassMap_existsUnique :
    ∃! k : exactVeroneseProj A π n h hne hgen ⟶ integralCurve W,
      k ≫ integralProjectiveMap W =
          completeOriginalProjectiveMap A π hne hgen n h L hL 2 s hs hcover ∧
        ∀ m, originalStageToCompatibleProj A π hne hgen n h m ≫ k = g m :=
  completeClosedTarget_existsUnique A π hne hgen n h (integralProjectiveMap W) _ g hg

/-- The reconstructed map into the original specified integral Weierstrass cubic. -/
def completeWeierstrassMap : exactVeroneseProj A π n h hne hgen ⟶ integralCurve W :=
  (completeWeierstrassMap_existsUnique A π hne hgen n h L hL s hs hcover W g hg).exists.choose

/-- The actual projective contraction is preserved by the reconstructed cubic map. -/
@[reassoc] theorem completeWeierstrassMap_projective :
    completeWeierstrassMap A π hne hgen n h L hL s hs hcover W g hg ≫
        integralProjectiveMap W =
      completeOriginalProjectiveMap A π hne hgen n h L hL 2 s hs hcover :=
  (completeWeierstrassMap_existsUnique A π hne hgen n h L hL s hs hcover W g hg)
    |>.exists.choose_spec.1

/-- Every supplied original finite-stage morphism is retained exactly. -/
@[reassoc] theorem completeWeierstrassMap_stage (m : ℕ) :
    originalStageToCompatibleProj A π hne hgen n h m ≫
        completeWeierstrassMap A π hne hgen n h L hL s hs hcover W g hg = g m :=
  (completeWeierstrassMap_existsUnique A π hne hgen n h L hL s hs hcover W g hg)
    |>.exists.choose_spec.2 m

/-- The reconstructed cubic map lies over the original arithmetic coefficient ring. -/
@[reassoc] theorem completeWeierstrassMap_toBase :
    completeWeierstrassMap A π hne hgen n h L hL s hs hcover W g hg ≫
      integralCurveStructure W = exactVeroneseProjToBase A π n h hne hgen := by
  rw [← integralProjectiveMap_baseProjection, ← Category.assoc,
    completeWeierstrassMap_projective, completeOriginalProjectiveMap_toBase]

/-- Original-stage marked maps determine the exact complete Weierstrass marking. -/
@[reassoc] theorem completeWeierstrassMap_marking (i : Fin n)
    (t : Spec (.of A) ⟶ integralCurve W)
    (ht : ∀ m, marking A π m n h i ≫ g m = baseToIntegral A π m ≫ t) :
    completeBaseMarking A π hne hgen n h i ≫
      completeWeierstrassMap A π hne hgen n h L hL s hs hcover W g hg = t := by
  apply completeBaseMarking_map_eq A π hgen hne n h
  intro m
  rw [completeWeierstrassMap_stage, ht m]

end FLT.Mazur.PolygonArithmeticStages
