/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientShear
public import FLT.Mazur.TensorOpenChartReparametrization

/-!
# The actual coefficient and shear isomorphisms of whole affine schemes

Both original tensor chart algebras yield scheme isomorphisms with the
sheared extended equations. Their original and extended coefficient maps
are retained without any domain hypothesis on the extended ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
local notation "V" => W.map (algebraMap R S)
local notation "U" => rootShearCurve V r
local notation "q" => algebraMap R S
local notation "D" => WeierstrassDilatation.Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6)
local notation "I" => WeierstrassModificationX.Coordinate U (q s) (q b3) (q b4 - r * q b3) (q b6)

/-- The full coefficient-extended sheared divided equation is the original tensor spectrum. -/
def dividedCoefficientShearIso : Spec (.of D) ≅
    Spec (.of (WeierstrassDilatation.ScalarExtension W s b3 b4 b6 S)) :=
  TensorOpenChart.algebraIso (dividedCoefficientShearEquiv W s b3 b4 b6 S r)

/-- The full coefficient-extended sheared incidence equation is the original tensor spectrum. -/
def incidenceCoefficientShearIso : Spec (.of I) ≅
    Spec (.of (WeierstrassModificationX.ScalarExtension W s b3 b4 b6 S)) :=
  TensorOpenChart.algebraIso (incidenceCoefficientShearEquiv W s b3 b4 b6 S r)

/-- The divided comparison retains the actual extended coefficient morphism. -/
@[reassoc] theorem dividedCoefficientShearIso_structure :
    (dividedCoefficientShearIso W s b3 b4 b6 S r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S
          (WeierstrassDilatation.ScalarExtension W s b3 b4 b6 S))) =
      Spec.map (CommRingCat.ofHom (algebraMap S D)) :=
  TensorOpenChart.algebraIso_structure _

/-- The incidence comparison retains the actual extended coefficient morphism. -/
@[reassoc] theorem incidenceCoefficientShearIso_structure :
    (incidenceCoefficientShearIso W s b3 b4 b6 S r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S
          (WeierstrassModificationX.ScalarExtension W s b3 b4 b6 S))) =
      Spec.map (CommRingCat.ofHom (algebraMap S I)) :=
  TensorOpenChart.algebraIso_structure _

/-- Every original divided function projects by coefficient extension followed by shear. -/
@[reassoc] theorem dividedCoefficientShearIso_projection :
    (dividedCoefficientShearIso W s b3 b4 b6 S r).hom ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom
        ((WeierstrassDilatation.shearForward V (q s) (q b3) (q b4) (q b6) r).toRingHom.comp
          (WeierstrassDilatation.coefficientMap W s b3 b4 b6 S).toRingHom)) := by
  apply TensorOpenChart.algebraIso_projection_of_tmul
  intro z
  exact (dividedCoefficientShearEquiv_tmul W s b3 b4 b6 S r 1 z).trans (one_smul _ _)

/-- Every original incidence function projects by the actual coefficient and shear substitution. -/
@[reassoc] theorem incidenceCoefficientShearIso_projection :
    (incidenceCoefficientShearIso W s b3 b4 b6 S r).hom ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom
        ((WeierstrassModificationX.shearForward V (q s) (q b3) (q b4) (q b6) r).toRingHom.comp
          (WeierstrassModificationX.coefficientMap W s b3 b4 b6 S).toRingHom)) := by
  apply TensorOpenChart.algebraIso_projection_of_tmul
  intro z
  exact (incidenceCoefficientShearEquiv_tmul W s b3 b4 b6 S r 1 z).trans (one_smul _ _)

end FLT.Mazur.WeierstrassDividedDepth
