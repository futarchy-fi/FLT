/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.WeierstrassSuccessiveXShear
public import FLT.Mazur.TensorOpenChartReparametrization

/-!
# Coefficient extension and shear of the whole successive incidence chart

The actual three-coordinate tensor equation is isomorphic to its sheared
coefficient extension. The horizontal coordinate is retained at zero as well.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
local notation "V" => W.map (algebraMap R S)
local notation "U" => rootShearCurve V r
local notation "q" => algebraMap R S
local notation "B" => WeierstrassSuccessiveX.Coordinate
  U (q s) (q π) (q b3) (q b4 - r * q b3) (q b6)

/-- The full successive tensor algebra is the actual sheared extended incidence equation. -/
def successiveCoefficientShearEquiv :
    WeierstrassSuccessiveX.ScalarExtension W s π b3 b4 b6 S ≃ₐ[S] B :=
  (WeierstrassSuccessiveX.baseChangeEquiv W s π b3 b4 b6 S).trans
    (WeierstrassSuccessiveX.shearEquiv V (q s) (q π) (q b3) (q b4) (q b6) r)

/-- Every pure tensor retains the original coefficient map followed by the full shear. -/
theorem successiveCoefficientShearEquiv_tmul
    (a : S) (z : WeierstrassSuccessiveX.Coordinate W s π b3 b4 b6) :
    successiveCoefficientShearEquiv W s π b3 b4 b6 S r (a ⊗ₜ[R] z) =
      a • WeierstrassSuccessiveX.shearForward V (q s) (q π) (q b3) (q b4) (q b6) r
        (WeierstrassSuccessiveX.coefficientMap W s π b3 b4 b6 S z) := by
  change WeierstrassSuccessiveX.shearForward V (q s) (q π) (q b3) (q b4) (q b6) r
    (a • WeierstrassSuccessiveX.coefficientMap W s π b3 b4 b6 S z) = _
  exact map_smul _ _ _

/-- The whole successive sheared equation is the actual original tensor spectrum. -/
def successiveCoefficientShearIso : Spec (.of B) ≅
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W s π b3 b4 b6 S)) :=
  TensorOpenChart.algebraIso (successiveCoefficientShearEquiv W s π b3 b4 b6 S r)

/-- The successive comparison retains its actual extended coefficient structure. -/
@[reassoc] theorem successiveCoefficientShearIso_structure :
    (successiveCoefficientShearIso W s π b3 b4 b6 S r).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap S
          (WeierstrassSuccessiveX.ScalarExtension W s π b3 b4 b6 S))) =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) :=
  TensorOpenChart.algebraIso_structure _

/-- All original successive functions project by the explicit coefficient and shear substitution. -/
@[reassoc] theorem successiveCoefficientShearIso_projection :
    (successiveCoefficientShearIso W s π b3 b4 b6 S r).hom ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom
        ((WeierstrassSuccessiveX.shearForward V (q s) (q π) (q b3) (q b4) (q b6) r).toRingHom.comp
          (WeierstrassSuccessiveX.coefficientMap W s π b3 b4 b6 S).toRingHom)) := by
  apply TensorOpenChart.algebraIso_projection_of_tmul
  intro z
  exact (successiveCoefficientShearEquiv_tmul W s π b3 b4 b6 S r 1 z).trans (one_smul _ _)

end FLT.Mazur.WeierstrassDividedDepth
