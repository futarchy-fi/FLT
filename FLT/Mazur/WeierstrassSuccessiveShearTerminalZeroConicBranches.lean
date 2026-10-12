/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalZeroNodeConic
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters
public import FLT.Mazur.PolygonCyclicNormalizationRanges
public import FLT.Mazur.WeierstrassDilatationShearNodeNormalForm
public import FLT.Mazur.NodalFiberNodeComparison

/-!
# Both scale-one terminal conic punctures retain reciprocal node coordinates

The whole conic boundary maps agree with the opposite full node branches
after inverting the projective parameter, over arbitrary coefficient fields.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S b6
local notation "C₀" => ConicCoordinate (U).a₁ c
local notation "B" => MiddleConicOpen U c
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
variable (h6 : algebraMap R S b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (k + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "ψ" => tensorShearScaleOneTerminalNodeConicMap W π k b3 b4 b6 S r
  hs hp h3 h4 hr h6 a ha
local notation "f₁" => conicBoundaryFirst U c hu h6
local notation "f₂" => conicBoundarySecond U c hu h6
open scoped LaurentPolynomial

/-- The entire first conic puncture is the reciprocal second node branch. -/
theorem tensorShearScaleOneTerminalConicFirst_eq : (f₁).comp ψ =
    (LaurentPolynomial.invert (R := S)).toAlgHom.comp
      (Polynomial.toLaurentAlg.comp PolygonNodeEqualizer.second) := by
  apply AlgHom.ext_of_adjoin_eq_top PolygonNodePresentation.a_adjoin
  intro z hz
  rcases hz with rfl | hz
  · change f₁ (ψ PolygonNodeLocalization.x) =
      LaurentPolynomial.invert (PolygonNodeLocalization.rightMap PolygonNodeLocalization.x)
    rw [tensorShearScaleOneTerminalNodeConicMap_first, map_mul, conicBoundaryFirst_v,
      mul_zero, PolygonNodeLocalization.rightMap_x, map_zero]
  · rcases hz with rfl
    change f₁ (ψ PolygonNodeLocalization.y) =
      LaurentPolynomial.invert (PolygonNodeLocalization.rightMap PolygonNodeLocalization.y)
    rw [tensorShearScaleOneTerminalNodeConicMap_second, map_mul, map_add, conicBoundaryFirst_v,
      AlgHom.commutes, zero_add, PolygonNodeLocalization.rightMap_y, LaurentPolynomial.invert_T]
    exact conicBoundaryFirst_inverse_mul U c hu h6

/-- The entire second conic puncture is the reciprocal first node branch. -/
theorem tensorShearScaleOneTerminalConicSecond_eq : (f₂).comp ψ =
    (LaurentPolynomial.invert (R := S)).toAlgHom.comp
      (Polynomial.toLaurentAlg.comp PolygonNodeEqualizer.first) := by
  apply AlgHom.ext_of_adjoin_eq_top PolygonNodePresentation.a_adjoin
  intro z hz
  rcases hz with rfl | hz
  · change f₂ (ψ PolygonNodeLocalization.x) =
      LaurentPolynomial.invert (PolygonNodeLocalization.leftMap PolygonNodeLocalization.x)
    rw [tensorShearScaleOneTerminalNodeConicMap_first, map_mul, conicBoundarySecond_v,
      PolygonNodeLocalization.leftMap_x, LaurentPolynomial.invert_T]
    exact conicBoundarySecond_inverse_mul U c hu h6
  · rcases hz with rfl
    change f₂ (ψ PolygonNodeLocalization.y) =
      LaurentPolynomial.invert (PolygonNodeLocalization.leftMap PolygonNodeLocalization.y)
    rw [tensorShearScaleOneTerminalNodeConicMap_second, map_mul, map_add, conicBoundarySecond_v,
      AlgHom.commutes, PolygonNodeLocalization.leftMap_y, map_zero]
    change _ * (-LaurentPolynomial.C (U).a₁ + LaurentPolynomial.C (U).a₁) = 0
    rw [neg_add_cancel, mul_zero]

open AlgebraicGeometry CategoryTheory
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "s₁" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁))
local notation "s₂" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂))

/-- The first puncture meets the opposite whole affine node branch by the actual overlap. -/
@[reassoc] theorem tensorShearScaleOneTerminalConicFirst_spec :
    s₁ ≫ s = ProjectiveLine.overlapRight S ≫ PolygonCyclicAtlas.secondBranch S := by
  rw [ProjectiveLine.overlapRight, Category.assoc, PolygonCyclicAtlas.overlap_secondBranch]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (tensorShearScaleOneTerminalConicFirst_eq W π k b3 b4 b6 S r hs hp h3 h4 hr h6 a ha)

/-- The second puncture keeps its opposite branch and the same reciprocal coordinate. -/
@[reassoc] theorem tensorShearScaleOneTerminalConicSecond_spec :
    s₂ ≫ s = ProjectiveLine.overlapRight S ≫ PolygonCyclicAtlas.firstBranch S := by
  rw [ProjectiveLine.overlapRight, Category.assoc, PolygonCyclicAtlas.overlap_firstBranch]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (tensorShearScaleOneTerminalConicSecond_eq W π k b3 b4 b6 S r hs hp h3 h4 hr h6 a ha)

end FLT.Mazur.WeierstrassSuccessiveX
