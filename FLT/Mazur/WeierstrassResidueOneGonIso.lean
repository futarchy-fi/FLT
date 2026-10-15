/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalOneGonCoordinates
public import FLT.Mazur.WeierstrassNodalResidueContraction
public import FLT.Mazur.WeierstrassInfinityResidueSmooth

/-!
# The entire original residue cubic retains its one-gon pinching

Transport through the proved residue equation. The comparison includes the
singular point, and its smooth restriction is the original reciprocal
infinity coordinate, with the actual integral coefficient morphism retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equation transport preserves the full original coefficient structure map. -/
@[reassoc] theorem equationCurveIso_inv_structure {K : Type} [CommRing K]
    {U V : WeierstrassCurve K} (h : U = V) :
    (equationCurveIso h).inv ≫ integralCurveStructure U = integralCurveStructure V := by
  subst V
  simp [equationCurveIso]

/-- Equation transport preserves the original projective infinity section. -/
@[reassoc] theorem equationCurveIso_inv_zero {K : Type} [CommRing K]
    {U V : WeierstrassCurve K} (h : U = V) :
    integralCurveZero V ≫ (equationCurveIso h).inv = integralCurveZero U := by
  subst V
  simp [equationCurveIso]

/-- Equation transport retains the full smooth inclusion, on every Laurent function. -/
@[reassoc] theorem splitEquationSmoothIso_curve {K : Type} [CommRing K]
    {U : WeierstrassCurve K} (a : Kˣ) (h : U = splitNodalEquation a) :
    splitNodalTorusToCurve a ≫ (equationCurveIso h).inv =
      (splitEquationSmoothIso a h).hom ≫ (integralSmoothOpen U).ι := by
  subst U
  simpa only [equationCurveIso, Iso.refl_inv, Category.comp_id, splitEquationSmoothIso,
    splitNodalRelativeSmoothIso, asIso_hom] using
    (splitNodalTorusToSmooth_inclusion a).symm

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 0 < depth)
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "a" => WeierstrassDilatation.residueTangentUnit D

/-- The original residue cubic, including its node, is the original pinched one-gon. -/
def residueOneGonIso : OneGonGluing.scheme K ≅ integralCurve V :=
  splitNodalOneGonIso a ≪≫ (equationCurveIso (splitDepth_residue_equation D hd)).symm

/-- The full comparison preserves the residue field. -/
@[reassoc] theorem residueOneGonIso_structure :
    (residueOneGonIso D hd).hom ≫ integralCurveStructure V = OneGonGluing.toBase K := by
  rw [residueOneGonIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    equationCurveIso_inv_structure, splitNodalOneGonIso_structure]

/-- The original pinching marking is the original residue infinity section. -/
@[reassoc] theorem residueOneGonIso_marking (i : Fin 1) :
    PolygonMarkedSections.sectionMap K 1 (OneGonNormalization.normalizationOver K) 1 i ≫
      (residueOneGonIso D hd).hom = integralCurveZero V := by
  rw [residueOneGonIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    splitNodalOneGonIso_marking, equationCurveIso_inv_zero]

/-- The full original-cubic comparison has exactly the reciprocal original smooth parameter. -/
@[reassoc] theorem residueOneGonIso_torus :
    OneGonGluing.torus K ≫ (residueOneGonIso D hd).hom =
      (ProjectiveLine.inversion K).hom ≫ (infinityResidueSmoothIso D hd).hom ≫
        (integralSmoothOpen V).ι := by
  rw [residueOneGonIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    splitNodalOneGonIso_torus, Category.assoc, splitEquationSmoothIso_curve]
  rfl

/-- The entire pinching comparison retains the actual integral contraction. -/
@[reassoc] theorem residueOneGonIso_contraction :
    (residueOneGonIso D hd).hom ≫ integralCoefficientMorphism W =
      (splitNodalOneGonIso a).hom ≫ nodalResidueContraction D hd := by
  simp only [residueOneGonIso, Iso.trans_hom, Iso.symm_hom,
    nodalResidueContraction, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart
