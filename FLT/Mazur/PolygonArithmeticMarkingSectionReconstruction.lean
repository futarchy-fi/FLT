/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticComparedSectionReconstruction
public import FLT.Mazur.PolygonArithmeticMarkedLineModel

/-!
# Reconstructing original arithmetic boundary sections in sealed line models

Compatible sections of the canonically modeled boundary lines algebraize
uniquely to the canonically modeled complete marking line. The canonical divisor-line
maps and the original arithmetic transitions at every order.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj family completeMarkedBoundaryModel
  exactVeroneseProj completeMarkedLineModel completeMarkedLineModelStageIso
  completeMarkedLineModelTransition completeLineStageTransitionIso
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Modeled original boundary sections recover a unique modeled complete marking section. -/
theorem completeMarkingSection_existsUnique
    (s : ∀ m, Γ(completeMarkedBoundaryModel A π n h m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (completeMarkedLineModelTransition A π n h (homOfLE hab)).hom.app ⊤
        (pullGlobal ((stageSystem A π n h).map (homOfLE hab)) _ (s b)) = s a) :
    ∃! t : Γ(completeMarkedLineModel A π hne hgen n h, ⊤), ∀ m,
      (completeMarkedLineModelStageIso A π hne hgen n h m).hom.app ⊤
        (pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) _ t) = s m := by
  exact completeLineComparedSection_existsUnique A π hne hgen n h _
    (completeMarkedLineModel_rankOne A π hne hgen n h)
    (fun m ↦ completeMarkedBoundaryModel A π n h m)
    (completeMarkedLineModelStageIso A π hne hgen n h)
    (fun f ↦ (completeMarkedLineModelTransition A π n h f).hom)
    (fun f ↦ completeMarkedLineModelStageIso_transition A π hne hgen n h f) s hs

/-- The original boundary restrictions detect every section of the actual marked line. -/
theorem completeMarkingSection_ext (s t : Γ(completeMarkedLineModel A π hne hgen n h, ⊤))
    (hst : ∀ m,
      (completeMarkedLineModelStageIso A π hne hgen n h m).hom.app ⊤
          (pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) _ s) =
        (completeMarkedLineModelStageIso A π hne hgen n h m).hom.app ⊤
          (pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) _ t)) : s = t := by
  apply completeLineSection_ext A π hne hgen n h _
    (completeMarkedLineModel_rankOne A π hne hgen n h)
  intro m
  exact (ConcreteCategory.bijective_of_isIso
    ((completeMarkedLineModelStageIso A π hne hgen n h m).hom.app ⊤)).injective (hst m)

end FLT.Mazur.PolygonArithmeticStages
