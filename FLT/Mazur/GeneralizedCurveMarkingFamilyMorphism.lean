/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyAffine
public import FLT.Mazur.GeneralizedCurveMarkingFrameCubicChange

/-!
# The whole original cubic morphism under a family isomorphism

Schematic density of the actual Cartier complement extends the coordinate
comparison across the original marking. The whole source may have higher
polygon fibers; neither whole-curve smoothness nor a unit discriminant is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve smoothMarkingChartRingEquiv smoothMarkingFamilyLift
  smoothMarkingFamilyFrame
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {E F : GeneralizedEllipticCurve S} (e : E ≅ F) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback ((s ≫ e.hom.group) ≫ F.inclusion).left).obj
    (divisorLineBundle ((s ≫ e.hom.group) ≫ F.inclusion).left.ker
      (smoothMarking_relativeCartier F (s ≫ e.hom.group)).1) ≅ structureModule S)
local notation "v" => (s ≫ e.hom.group) ≫ F.inclusion
local notation "hJ" => And.left (smoothMarking_relativeCartier F (s ≫ e.hom.group))
local notation "φ" => smoothMarkingComplementBaseMap F (s ≫ e.hom.group)
local notation "x" => smoothMarkingComplementX F (s ≫ e.hom.group) b
local notation "y" => smoothMarkingComplementY F (s ≫ e.hom.group) b
local notation "fx" => relativePoleFunction F.curve.hom (Over.Hom.left (v)) (hJ) 2
  (smoothMarkingFamilyLift e s a 1 (by decide))
local notation "fy" => relativePoleFunction F.curve.hom (Over.Hom.left (v)) (hJ) 3
  (smoothMarkingFamilyLift e s a 2 (by decide))
local notation "π" => smoothMarkingFamilyComplementMap e s
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "u" => frameComparisonUnit b (smoothMarkingFamilyFrame e s a) ⊤

open WeierstrassIntegralChart
attribute [local irreducible] affineVariableChangeMap smoothMarkingFamilyChange
  smoothMarkingFamilyComplementMap smoothMarkingComplementBaseMap
local notation "V" => smoothMarkingWeierstrassCurve F (s ≫ e.hom.group) b
local notation "C" => smoothMarkingFamilyChange e s a b
local notation "hC" => And.left (And.right (smoothMarkingFamilyChange_spec e s a b))
local notation "Q" => smoothMarkingChartRingEquiv E s a
local notation "Q'" => smoothMarkingChartRingEquiv F (s ≫ e.hom.group) b

local notation "ι" => Scheme.Opens.ι (X := E.curve.left)
  (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (s ≫ E.inclusion)))))
local notation "ι'" => Scheme.Opens.ι (X := F.curve.left)
  (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left ((s ≫ e.hom.group) ≫ F.inclusion)))))

/-- Independently recomputed whole cubic maps retain the actual original family isomorphism. -/
theorem smoothMarkingToIntegralCubic_familyIso :
    smoothMarkingToIntegralCubic F (s ≫ e.hom.group) b ≫
      (smoothMarkingFamilyCubicIso e s a b).hom =
        e.inv.curve.left ≫ smoothMarkingToIntegralCubic E s a := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion S.isoSpec.hom
  let _ : LocallyOfFinitePresentation F.curve.hom := F.family.family.2.2
  let _ : IsLocallyNoetherian F.curve.left :=
    LocallyOfFiniteType.isLocallyNoetherian F.curve.hom
  apply cartierComplement_hom_ext (smoothMarking_relativeCartier F (s ≫ e.hom.group)).1
    (integralCurveStructure (W))
  · rw [Category.assoc (smoothMarkingToIntegralCubic F (s ≫ e.hom.group) b),
      smoothMarkingFamilyCubicIso_over, smoothMarkingToIntegralCubic_over,
      Category.assoc e.inv.curve.left, smoothMarkingToIntegralCubic_over,
      ← Category.assoc e.inv.curve.left, e.inv.curve.w]
  · rw [← Category.assoc (ι'),
      ← smoothMarkingToIntegralAffineChart_cubic F (s ≫ e.hom.group) b,
      Category.assoc (smoothMarkingToIntegralAffineChart F (s ≫ e.hom.group) b),
      smoothMarkingFamilyCubicIso_affine,
      ← Category.assoc (smoothMarkingToIntegralAffineChart F (s ≫ e.hom.group) b),
      smoothMarkingToIntegralAffineChart_familyIso, Category.assoc (π),
      smoothMarkingToIntegralAffineChart_cubic E s a, ← Category.assoc (π),
      smoothMarkingFamilyComplementMap_ι, Category.assoc (ι')]

/-- Existence of the constructed pointed comparison, retaining the actual whole-curve square. -/
theorem exists_smoothMarkingFamilyCubicIso :
    ∃ i : integralCurve (V) ≅ integralCurve (W),
      i.hom ≫ integralCurveStructure (W) = integralCurveStructure (V) ∧
      integralCurveZero (V) ≫ i.hom = integralCurveZero (W) ∧
      smoothMarkingToIntegralCubic F (s ≫ e.hom.group) b ≫ i.hom =
        e.inv.curve.left ≫ smoothMarkingToIntegralCubic E s a :=
  ⟨smoothMarkingFamilyCubicIso e s a b, smoothMarkingFamilyCubicIso_over e s a b,
    smoothMarkingFamilyCubicIso_zero e s a b, smoothMarkingToIntegralCubic_familyIso e s a b⟩

end FLT.Mazur.GeneralizedEllipticCurve
