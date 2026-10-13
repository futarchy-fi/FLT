/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialBoundaryHomExt
public import FLT.Mazur.WeierstrassConicZeroProjectiveDescent
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing

/-!
# Descent across the full initial tensor overlap

The complete initial conic and the first retained lines agree through the
original signed reciprocal transitions on the entire overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S d.b3 = 0) (g4 : algebraMap R S d.b4 = 0)
  (g6 : algebraMap R S d.b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S d.b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "x" => WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6
local notation "t₀" => t W (π ^ k) d.b3 d.b4 d.b6
local notation "u₀" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t₀
  (overlapEquiv W (π ^ k) d.b3 d.b4 d.b6)
local notation "B" => PrincipalOpenTensor.transitionIso S x u₀ (previousBoundaryEquiv hπ d e)
local notation "E" => tensorShearInitialConicBoundaryIso W (π ^ k)
  d.b3 d.b4 d.b6 S r hs g3 g4 hr
local notation "H" => tensorShearLineToHorizontal W (π ^ k) π
  e.b3 e.b4 e.b6 S r hs hp h3 h4 hr
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom)
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom)
local notation "b₁" => Spec.map (CommRingCat.ofHom (conicBoundaryFirst U c hu g6).toRingHom)
local notation "b₂" => Spec.map (CommRingCat.ofHom (conicBoundarySecond U c hu g6).toRingHom)

local notation "F" => tensorShearInitialConicMap W (π ^ k) d.b3 d.b4 d.b6
  S r hs g3 g4 hr
local notation "p₁" => (conicZeroAffineIso c g6).hom ≫
  (conicFirstParameterIso (U).a₁ c hu).inv ≫ conicFirstOpenImmersion (U).a₁ c
local notation "p₂" => (conicZeroAffineIso c g6).hom ≫
  (conicSecondParameterIso (U).a₁ c hu).inv ≫ conicSecondOpenImmersion (U).a₁ c
local notation "L" => fun v hv => Spec.map (CommRingCat.ofHom
  (tensorShearLineMap W (π ^ k) π e.b3 e.b4 e.b6 S r hs hp h3 h4 hr v hv).toRingHom)
variable {Y : Scheme.{u}} (f₁ f₂ : ProjectiveLine.scheme S ⟶ Y)
  (f : Spec (.of (WeierstrassModificationX.ScalarExtension W (π ^ k)
    d.b3 d.b4 d.b6 S)) ⟶ Y)
  (g : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ k) π
    e.b3 e.b4 e.b6 S)) ⟶ Y)

/-- Full branch restrictions force compatibility on the full original initial overlap. -/
theorem coefficientShearInitialBoundary_desc
    (hf₁ : p₁ ≫ Spec.map (CommRingCat.ofHom (F).toRingHom) ≫ f =
      ProjectiveLine.left S ≫ f₁)
    (hf₂ : p₂ ≫ Spec.map (CommRingCat.ofHom (F).toRingHom) ≫ f =
      ProjectiveLine.left S ≫ f₂)
    (hg₁ : L 0 (middle_first_root U) ≫ g =
      ProjectiveLine.chartScaling S a ≫ ProjectiveLine.right S ≫ f₁)
    (hg₂ : L (-(U).a₁) (middle_second_root U) ≫ g =
      ProjectiveLine.chartScaling S (-a) ≫ ProjectiveLine.right S ≫ f₂) :
    (A).inv ≫ PrincipalOpenTensor.inclusion S t₀ ≫ f =
      (B).inv ≫ PrincipalOpenTensor.inclusion S u₀ ≫ g := by
  apply coefficientShearInitialBoundary_hom_ext
    hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← coefficientShearInitialFirstLine_boundary_spec_assoc
      hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha]
    have hb : Spec.map (CommRingCat.ofHom (conicPuncturedFirst U c g6).toRingHom) =
        ProjectiveLine.overlapLeft S ≫ p₁ := by
      rw [conicPuncturedFirst_spec c g6 U hu, ← conicZeroAffineIso_puncture c g6]
      simp only [Category.assoc]
    rw [hb]
    simp only [Category.assoc] at hf₁ ⊢
    rw [hf₁, tensorShearLineToHorizontal_comp_assoc, hg₁]
    change _ = ρ₁ ≫ ProjectiveLine.overlapLeft S ≫
      ProjectiveLine.chartScaling S a ≫ ProjectiveLine.right S ≫ f₁
    rw [ProjectiveLine.scaledReciprocal_overlap_assoc]
    rw [← Category.assoc (ProjectiveLine.chartScaling S a⁻¹),
      ← ProjectiveLine.chartScaling_mul, inv_mul_cancel, ProjectiveLine.chartScaling_one,
      Category.id_comp]
    simp only [← Category.assoc]
    exact congrArg (· ≫ f₁) (ProjectiveLine.overlap_condition S)
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← coefficientShearInitialSecondLine_boundary_spec_assoc
      hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha]
    have hb : Spec.map (CommRingCat.ofHom (conicPuncturedSecond U c g6).toRingHom) =
        ProjectiveLine.overlapLeft S ≫ p₂ := by
      rw [conicPuncturedSecond_spec c g6 U hu, ← conicZeroAffineIso_puncture c g6]
      simp only [Category.assoc]
    rw [hb]
    simp only [Category.assoc] at hf₂ ⊢
    rw [hf₂, tensorShearLineToHorizontal_comp_assoc, hg₂]
    change _ = ρ₂ ≫ ProjectiveLine.overlapLeft S ≫
      ProjectiveLine.chartScaling S (-a) ≫ ProjectiveLine.right S ≫ f₂
    rw [ProjectiveLine.scaledReciprocal_overlap_assoc]
    rw [← Category.assoc (ProjectiveLine.chartScaling S (-a)⁻¹),
      ← ProjectiveLine.chartScaling_mul, inv_mul_cancel, ProjectiveLine.chartScaling_one,
      Category.id_comp]
    simp only [← Category.assoc]
    exact congrArg (· ≫ f₂) (ProjectiveLine.overlap_condition S)

end FLT.Mazur.WeierstrassDividedDepth
