/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineRegularCoordinates
public import FLT.FreyCurve.Serre.VeluGenericChartMorphism

/-!
# A regular Vélu morphism on an explicit open of the actual cubic

The original formulas define a morphism into the actual target cubic on the
principal denominator open. Its generic restriction is the original morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The explicit denominator open embeds in the actual original cubic. -/
def veluAffineOpenImmersion : Spec (.of (VeluAffineLocalization E G)) ⟶ integralCurve E :=
  Spec.map (CommRingCat.ofHom (algebraMap _ (VeluAffineLocalization E G))) ≫
    integralCurveChart E 2

/-- This domain is an actual open subscheme of the original source curve. -/
instance veluAffineOpenImmersion_isOpenImmersion : IsOpenImmersion (veluAffineOpenImmersion E G) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ integralCurveChart E 2))

variable (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The target coordinate ring evaluated at the regular original Vélu functions. -/
def veluAffineRegularChart : Coordinate (curve E G) 2 →ₐ[K] VeluAffineLocalization E G :=
  evaluation (curve E G) 2 ![veluAffineX E G, veluAffineY E G, 1]
    ((Projective.equation_some _ _).mpr (veluAffine_equation E G hodd)) rfl

/-- The localized chart retains exactly the original generic coordinate homomorphism. -/
theorem veluAffineRegularChart_generic :
    (veluAffineLocalizationHom E G).comp (veluAffineRegularChart E G hodd) =
      veluGenericChart E G hodd := by
  apply hom_ext
  intro i
  fin_cases i
  · change veluAffineLocalizationHom E G
      (veluAffineRegularChart E G hodd (coord (curve E G) 2 0)) =
        veluGenericChart E G hodd (coord (curve E G) 2 0)
    rw [veluAffineRegularChart, evaluation_coord, veluGenericChart_x]
    exact veluAffineX_generic E G
  · change veluAffineLocalizationHom E G
      (veluAffineRegularChart E G hodd (coord (curve E G) 2 1)) =
        veluGenericChart E G hodd (coord (curve E G) 2 1)
    rw [veluAffineRegularChart, evaluation_coord, veluGenericChart_y]
    exact veluAffineY_generic E G
  · change ((veluAffineLocalizationHom E G).comp (veluAffineRegularChart E G hodd))
      (coord (curve E G) 2 2) = veluGenericChart E G hodd (coord (curve E G) 2 2)
    rw [coord_self, map_one, map_one]

/-- The original Vélu formulas are regular on the explicit denominator open. -/
def veluAffineRegularMorphism :
    Spec (.of (VeluAffineLocalization E G)) ⟶ integralCurve (curve E G) :=
  Spec.map (CommRingCat.ofHom (veluAffineRegularChart E G hodd).toRingHom) ≫
    integralCurveChart (curve E G) 2

/-- The regular extension is over the original coefficient field. -/
@[reassoc] theorem veluAffineRegularMorphism_base :
    veluAffineRegularMorphism E G hodd ≫ integralCurveStructure (curve E G) =
      veluAffineOpenImmersion E G ≫ integralCurveStructure E := by
  simp only [veluAffineRegularMorphism, veluAffineOpenImmersion, Category.assoc,
    integralCurveChart_structure]
  exact (specAlgHom_structure _).trans (specAlgHom_structure
    (IsScalarTower.toAlgHom K (Coordinate E 2) (VeluAffineLocalization E G))).symm

/-- The generic restriction is precisely the original generic Vélu morphism. -/
@[reassoc] theorem veluAffineRegularMorphism_generic :
    Spec.map (CommRingCat.ofHom (veluAffineLocalizationHom E G).toRingHom) ≫
        veluAffineRegularMorphism E G hodd = veluGenericMorphism E G hodd := by
  rw [veluAffineRegularMorphism, ← Spec.map_comp_assoc]
  have h := congrArg AlgHom.toRingHom (veluAffineRegularChart_generic E G hodd)
  change Spec.map (CommRingCat.ofHom
    ((veluAffineLocalizationHom E G).comp (veluAffineRegularChart E G hodd)).toRingHom) ≫ _ = _
  rw [h]
  rfl

end WeierstrassCurve.Velu
