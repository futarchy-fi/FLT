/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicCocycle
public import FLT.Mazur.GeneralizedCurveMarkedCubicNaturality
public import FLT.Mazur.GeneralizedCurveMarkingOverlapRefinement

/-!
# Cubic overlap refinements retain the actual family associators

Recomputing the overlap after a common refinement agrees with pulling back its
full-family comparison. The square includes both original family associators
and four independently chosen frames on the refined families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve markedCubicComparison
variable {S T U V Z : Scheme} [IsAffine Z] [IsNoetherianRing Γ(Z, ⊤)]
  (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ S) (p : V ⟶ T) (q : V ⟶ U)
  (p' : Z ⟶ T) (q' : Z ⟶ U) (m : Z ⟶ V)
  (w : q ≫ h = p ≫ g) (w' : q' ≫ h = p' ≫ g)
  (hp : p' = m ≫ p) (hq : q' = m ≫ q)
  (s : 𝟙_ (Over S) ⟶ E.group)
  (a : SmoothMarkingFrame ((E.baseChange g).baseChange p') (pullSection p' (pullSection g s)))
  (b : SmoothMarkingFrame ((E.baseChange h).baseChange q') (pullSection q' (pullSection h s)))
  (c : SmoothMarkingFrame (((E.baseChange g).baseChange p).baseChange m)
    (pullSection m (pullSection p (pullSection g s))))
  (d : SmoothMarkingFrame (((E.baseChange h).baseChange q).baseChange m)
    (pullSection m (pullSection q (pullSection h s))))
local notation "e" => Iso.app (baseChangeSquare g h q p w) E
local notation "e'" => Iso.app (baseChangeSquare g h q' p' w') E
local notation "L" => baseChangeCompEqIso (E.baseChange g) p m p' hp
local notation "R" => baseChangeCompEqIso (E.baseChange h) q m q' hq
local notation "sL" => pullSection p' (pullSection g s)
local notation "sR" => pullSection q' (pullSection h s)
local notation "tL" => pullSection m (pullSection p (pullSection g s))
local notation "tR" => pullSection m (pullSection q (pullSection h s))
local notation "hL" => baseChangeCompEqIso_groupSection (E.baseChange g)
  p m p' hp (pullSection g s)
local notation "hR" => baseChangeCompEqIso_groupSection (E.baseChange h)
  q m q' hq (pullSection h s)
local notation "he'" => smoothMarkingOverlap_group E g h p' q' w' s
local notation "he" => markedFamily_baseChange_section m e
  (pullSection q (pullSection h s)) (pullSection p (pullSection g s))
  (smoothMarkingOverlap_group E g h p q w s)

/-- The constructed refined cubic square retains both actual full-family associators. -/
theorem smoothMarkingOverlap_cubicRefine :
    markedCubicComparison L sL tL hL a c ≪≫ markedCubicComparison e' sR sL he' b a =
      markedCubicComparison ((baseChangeFunctor m).mapIso e) tR tL he d c ≪≫
        markedCubicComparison R sR tR hR b d := by
  rw [markedCubicComparison_comp, markedCubicComparison_comp]
  congr 1
  exact smoothMarkingOverlap_refine E g h p q p' q' m w w' hp hq

end FLT.Mazur.GeneralizedEllipticCurve
