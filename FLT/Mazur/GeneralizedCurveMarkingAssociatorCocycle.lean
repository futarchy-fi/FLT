/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAssociatorCubic
public import FLT.Mazur.GeneralizedCurveMarkingAssociatorSquare
public import FLT.Mazur.GeneralizedCurveMarkingCubicExt
public import FLT.Mazur.GeneralizedCurveMarkingCubicProjection

/-!
# The cubic cocycle for independently iterated families

For arbitrary independent frames on the original, intermediate, direct and
iterated families, the constructed pointed associator comparison makes the
two cubic projection routes equal. The actual whole-curve maps detect this
equality, so higher polygons and nonreduced coefficient rings remain allowed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve smoothMarkingCubicProjection
variable {S T U : Scheme}
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  [IsAffine U] [IsNoetherianRing Γ(U, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (h : U ⟶ T)
  (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback ((pullSection g s) ≫ (E.baseChange g).inclusion).left).obj
    (divisorLineBundle ((pullSection g s) ≫ (E.baseChange g).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
  (d : (pullback ((pullSection (h ≫ g) s) ≫ (E.baseChange (h ≫ g)).inclusion).left).obj
    (divisorLineBundle ((pullSection (h ≫ g) s) ≫ (E.baseChange (h ≫ g)).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange (h ≫ g))
        (pullSection (h ≫ g) s)).1) ≅ structureModule U)
  (c : (pullback (pullSection h (pullSection g s) ≫
    ((E.baseChange g).baseChange h).inclusion).left).obj
    (divisorLineBundle (pullSection h (pullSection g s) ≫
      ((E.baseChange g).baseChange h).inclusion).left.ker
      (smoothMarking_relativeCartier ((E.baseChange g).baseChange h)
        (pullSection h (pullSection g s))).1) ≅ structureModule U)
local notation "D" => E.baseChange (h ≫ g)
local notation "F" => GeneralizedEllipticCurve.baseChange (E.baseChange g) h
local notation "sD" => pullSection (h ≫ g) s
local notation "sF" => pullSection h (pullSection g s)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "WD" => smoothMarkingWeierstrassCurve D sD d
local notation "WF" => smoothMarkingWeierstrassCurve F sF c
local notation "PG" => smoothMarkingCubicProjection E g s a b
local notation "PH" => smoothMarkingCubicProjection (E.baseChange g) h (pullSection g s) b c
local notation "PD" => smoothMarkingCubicProjection E (h ≫ g) s a d

/-- Successive cubic projections retain the composite map of coefficient spectra. -/
theorem smoothMarkingIteratedCubic_square :
    (PH ≫ PG) ≫ integralCurveStructure W =
      integralCurveStructure WF ≫ Spec.map (h ≫ g).appTop := by
  rw [Category.assoc, smoothMarkingCubicProjection_over,
    ← Category.assoc (PH), smoothMarkingCubicProjection_over]
  simp only [Scheme.Hom.comp_appTop, Spec.map_comp, Category.assoc]

/-- The successive route as an actual morphism to the directly pulled-back original cubic. -/
def smoothMarkingIteratedCubicLift :
    integralCurve WF ⟶ Limits.pullback (integralCurveStructure W) (Spec.map (h ≫ g).appTop) :=
  Limits.pullback.lift (PH ≫ PG) (integralCurveStructure WF)
    (smoothMarkingIteratedCubic_square E g h s a b c)

/-- The constructed pointed associator makes direct and successive cubic projections equal. -/
theorem smoothMarkingAssociator_cubicCocycle :
    ∃ i : integralCurve WF ≅ integralCurve WD,
      i.hom ≫ integralCurveStructure WD = integralCurveStructure WF ∧
      integralCurveZero WF ≫ i.hom = integralCurveZero WD ∧
      i.hom ≫ PD = PH ≫ PG ∧
      smoothMarkingToIntegralCubic F sF c ≫ i.hom =
        (E.baseChangeCompIso g h).inv.curve.left ≫ smoothMarkingToIntegralCubic D sD d := by
  obtain ⟨i, ho, hz, hw⟩ := smoothMarkingAssociator_cubic E g h s d c
  refine ⟨i, ho, hz, ?_, hw⟩
  apply smoothMarkingToIntegralCubic_hom_ext F sF c (integralCurveStructure W)
  · simp only [Category.assoc, smoothMarkingCubicProjection_over]
    rw [← Category.assoc i.hom, ho,
      ← Category.assoc (PH), smoothMarkingCubicProjection_over]
    simp only [Scheme.Hom.comp_appTop, Spec.map_comp, Category.assoc]
  · rw [← Category.assoc (smoothMarkingToIntegralCubic F sF c), hw,
      Category.assoc (E.baseChangeCompIso g h).inv.curve.left,
      smoothMarkingToIntegralCubic_projection,
      ← Category.assoc (smoothMarkingToIntegralCubic F sF c),
      smoothMarkingToIntegralCubic_projection, Category.assoc,
      smoothMarkingToIntegralCubic_projection]
    rw [← Category.assoc, ← smoothMarkingAssociator_projection, Category.assoc]

/-- The constructed associator also identifies the actual categorical pullback morphisms. -/
theorem smoothMarkingAssociator_cubicPullback :
    ∃ i : integralCurve WF ≅ integralCurve WD,
      i.hom ≫ integralCurveStructure WD = integralCurveStructure WF ∧
      integralCurveZero WF ≫ i.hom = integralCurveZero WD ∧
      i.hom ≫ (smoothMarkingCubicPullbackIso E (h ≫ g) s a d).hom =
        smoothMarkingIteratedCubicLift E g h s a b c ∧
      smoothMarkingToIntegralCubic F sF c ≫ i.hom =
        (E.baseChangeCompIso g h).inv.curve.left ≫ smoothMarkingToIntegralCubic D sD d := by
  obtain ⟨i, ho, hz, hc, hw⟩ := smoothMarkingAssociator_cubicCocycle E g h s a b d c
  refine ⟨i, ho, hz, ?_, hw⟩
  apply Limits.pullback.hom_ext
  · simpa only [smoothMarkingCubicProjection, Category.assoc, smoothMarkingIteratedCubicLift,
      Limits.pullback.lift_fst] using hc
  · rw [Category.assoc, smoothMarkingCubicPullbackIso_snd, ho,
      smoothMarkingIteratedCubicLift, Limits.pullback.lift_snd]

end FLT.Mazur.GeneralizedEllipticCurve
