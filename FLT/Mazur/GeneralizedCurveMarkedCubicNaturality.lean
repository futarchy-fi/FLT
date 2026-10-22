/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicComparison
public import FLT.Mazur.GeneralizedCurveMarkingCubicProjection
public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence

/-!
# Base-change naturality of the constructed marked cubic comparison

An actual family isomorphism and its base change yield the same cubic map after
projection. All four frames are independent. The proof retains the original
whole-curve square, with no smoothness assumption on the whole family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve markedCubicComparison
variable {S T : Scheme} (g : T ⟶ S) {E F : GeneralizedEllipticCurve S}
  (e : E ≅ F) (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
  (hs : s ≫ e.hom.group = t)

include hs in
/-- The actual base-changed family isomorphism preserves the pulled original marking. -/
theorem markedFamily_baseChange_section :
    pullSection g s ≫ ((baseChangeFunctor g).mapIso e).hom.group = pullSection g t := by
  change pullSection g s ≫ (Over.pullback g).map e.hom.group = _
  rw [← section_comp, hs]

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (a : SmoothMarkingFrame E s) (b : SmoothMarkingFrame F t)
  (c : SmoothMarkingFrame (E.baseChange g) (pullSection g s))
  (d : SmoothMarkingFrame (F.baseChange g) (pullSection g t))
local notation "eT" => Functor.mapIso (baseChangeFunctor g) e
local notation "CT" => markedCubicComparison (E := E.baseChange g) (F := F.baseChange g)
  eT (pullSection g s) (pullSection g t)
  (markedFamily_baseChange_section g e s t hs) c d
local notation "CS" => markedCubicComparison e s t hs a b
local notation "PE" => smoothMarkingCubicProjection E g s a c
local notation "PF" => smoothMarkingCubicProjection F g t b d

/-- Independently recomputed comparisons commute with the actual cubic base projection. -/
theorem markedCubicComparison_baseChange : (CT).hom ≫ PE = PF ≫ (CS).hom := by
  apply smoothMarkingToIntegralCubic_hom_ext (F.baseChange g) (pullSection g t) d
    (integralCurveStructure (smoothMarkingWeierstrassCurve E s a))
  · simp only [Category.assoc, smoothMarkingCubicProjection_over,
      markedCubicComparison_over, markedCubicComparison_over_assoc]
  · rw [← Category.assoc, markedCubicComparison_whole, Category.assoc,
      smoothMarkingToIntegralCubic_projection,
      ← Category.assoc (smoothMarkingToIntegralCubic (F.baseChange g) (pullSection g t) d),
      smoothMarkingToIntegralCubic_projection, Category.assoc, markedCubicComparison_whole]
    change (baseChangeMap g e.inv).curve.left ≫
      Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToIntegralCubic E s a = _
    rw [← Category.assoc, baseChangeMap_fst, Category.assoc]

end FLT.Mazur.GeneralizedEllipticCurve
