/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeAffine
public import FLT.Mazur.GeneralizedCurveMarkingFrameCubicChange
public import FLT.Mazur.WeierstrassIntegralBaseChange

/-!
# Base change of the entire original cubic morphism

Schematic density of the actual Cartier complement extends the affine
comparison across the marking. No smoothness of the entire curve is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve smoothMarkingChartRingEquiv smoothMarkingTransportedLift
  smoothMarkingTransportedFrame affineVariableChangeMap smoothMarkingBaseChangeChange
  smoothMarkingComplementProjection smoothMarkingComplementBaseMap
variable {S T : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback (pullSection g s ≫ (E.baseChange g).inclusion).left).obj
    (divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "V" => smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b
local notation "C" => smoothMarkingBaseChangeChange E g s a b
local notation "hC" => And.left (And.right (smoothMarkingBaseChangeChange_spec E g s a b))
local notation "π" => smoothMarkingComplementProjection E g s
local notation "Q" => smoothMarkingChartRingEquiv E s a
local notation "Q'" => smoothMarkingChartRingEquiv (E.baseChange g) (pullSection g s) b

local notation "ι" => Scheme.Opens.ι (X := E.curve.left)
  (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (s ≫ E.inclusion)))))
local notation "ι'" => Scheme.Opens.ι
  (X := Over.left (GeneralizedEllipticCurve.curve (E.baseChange g)))
  (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support (Scheme.Hom.ker (Over.Hom.left
    (pullSection g s ≫ GeneralizedEllipticCurve.inclusion (E.baseChange g))))))

/-- Arbitrary base change commutes with the actual whole-curve cubic morphism. -/
theorem smoothMarkingToIntegralCubic_baseChange :
    let _ := g.appTop.hom.toAlgebra
    smoothMarkingToIntegralCubic (E.baseChange g) (pullSection g s) b ≫
      (smoothMarkingBaseChangeCubicIso E g s a b).hom ≫ integralCoefficientMorphism (W) =
        Limits.pullback.fst E.curve.hom g ≫ smoothMarkingToIntegralCubic E s a := by
  let _ := g.appTop.hom.toAlgebra
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  let _ : LocallyOfFinitePresentation (E.baseChange g).curve.hom :=
    (E.baseChange g).family.family.2.2
  let _ : IsLocallyNoetherian (E.baseChange g).curve.left :=
    LocallyOfFiniteType.isLocallyNoetherian (E.baseChange g).curve.hom
  apply cartierComplement_hom_ext
    (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1
    (integralCurveStructure (W))
  · simp only [Category.assoc, integralCoefficientMorphism_structure]
    change smoothMarkingToIntegralCubic (E.baseChange g) (pullSection g s) b ≫
      (smoothMarkingBaseChangeCubicIso E g s a b).hom ≫
        integralCurveStructure ((W).map g.appTop.hom) ≫ Spec.map g.appTop = _
    rw [smoothMarkingBaseChangeCubicIso_over_assoc,
      smoothMarkingToIntegralCubic_over_assoc, smoothMarkingToIntegralCubic_over,
      ← Scheme.toSpecΓ_naturality, ← Category.assoc,
      ← (smoothMarkingBaseChange_cartesian E g).w, Category.assoc]
  · have hπ : (π) ≫ (ι) = (ι') ≫ Limits.pullback.fst E.curve.hom g := by
      unfold smoothMarkingComplementProjection
      exact sectionPointComplementMap_ι (smoothMarkingBaseChange_cartesian E g)
        (s ≫ E.inclusion).left
        (pullSection g s ≫ (E.baseChange g).inclusion).left
        (s ≫ E.inclusion).w (pullSection g s ≫ (E.baseChange g).inclusion).w
        (smoothMarkingBaseChange_sectionSquare E g s)
    rw [← Category.assoc,
      ← smoothMarkingToIntegralAffineChart_cubic (E.baseChange g) (pullSection g s) b,
      Category.assoc, smoothMarkingBaseChangeCubicIso_affine_assoc E g s a b]
    erw [integralCurveChart_coefficientMorphism (S := Γ(T, ⊤)) (W) 2]
    change _ ≫ (affineVariableChangeIso ((W).map g.appTop.hom) (V) (C) (hC)).hom ≫
      Spec.map (CommRingCat.ofHom (chartCoefficientRingMap g.appTop.hom (W) 2)) ≫
        integralCurveChart (W) 2 = _
    have ha := congrArg (fun k => k ≫ integralCurveChart (W) 2)
      (smoothMarkingToIntegralAffineChart_baseChange E g s a b)
    simp only [Category.assoc, smoothMarkingToIntegralAffineChart_cubic] at ha
    rw [← Category.assoc (π), hπ, Category.assoc] at ha
    exact ha

end FLT.Mazur.GeneralizedEllipticCurve
