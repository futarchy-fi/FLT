/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentChartMap
public import FLT.Mazur.WeierstrassConicZeroPunctureCover
public import FLT.Mazur.WeierstrassConicZeroProjectiveDescent
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing

/-!
# Descent on the entire original adjacent boundary

The complete preceding conic and both full next lines impose compatibility
through their original signed reciprocal transitions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ}
  (d : Data W π (k + 1)) (e : Data W π (k + 1 + 1))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S e.b3 = 0) (h4 : algebraMap R S e.b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := k)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "c" => algebraMap R S d.b6
local notation "φ" => tensorShearDividedConicOpenEquiv W (π ^ k) π
  d.b3 d.b4 d.b6 S r hs hp g3 g4 hr
local notation "E" => tensorAdjacentBoundaryEquiv hπ d e S
local notation "H" => Localization.Away (tensorCoord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S 2)
local notation "B" => MiddleConicOpen U c
local notation "i" => PrincipalOpenTensor.inclusion S (coord W (π ^ (k + 1)) π e.b3 e.b4 e.b6 2)
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))

local notation "J" => coefficientShearAdjacentConicIso hπ d e S r hs hp hr
variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "b₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst U c hu gc)))
local notation "b₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond U c hu gc)))
local notation "ρ₁" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv (a⁻¹)))))
local notation "ρ₂" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv ((-a)⁻¹)))))
local notation "l₁" => tensorShearLineToHorizontal W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr 0 (middle_first_root U)
local notation "l₂" => tensorShearLineToHorizontal W (π ^ (k + 1)) π
  e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
  (-WeierstrassCurve.a₁ U) (middle_second_root U)
local notation "L₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (tensorShearLineMap W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
    0 (middle_first_root U))))
local notation "L₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (tensorShearLineMap W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S r hsNext hp h3 h4 hr
    (-WeierstrassCurve.a₁ U) (middle_second_root U))))

local notation "N" => coefficientShearAdjacentConicToNext hπ d e S r hs hp hr
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "C₀" => ConicCoordinate (U).a₁ c
local notation "T₀" => ScalarExtension W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S
variable {Y : Scheme.{u}} (f₁ f₂ : ProjectiveLine.scheme S ⟶ Y)
  (g : Spec (.of (ScalarExtension W (π ^ (k + 1)) π e.b3 e.b4 e.b6 S)) ⟶ Y)
local notation "D" => conicZeroProjectiveDesc (U).a₁ c hu gc f₁ f₂

/-- The full conic boundary agrees with the next map from its two entire line restrictions. -/
theorem coefficientShearAdjacentBoundary_desc
    (hg₁ : L₁ ≫ g = ProjectiveLine.chartScaling S a ≫ ProjectiveLine.right S ≫ f₁)
    (hg₂ : L₂ ≫ g = ProjectiveLine.chartScaling S (-a) ≫ ProjectiveLine.right S ≫ f₂) :
    inc ≫ D = N ≫ g := by
  apply conicZeroBoundary_hom_ext U c hu gc
  · rw [conicZeroBoundaryFirst_parameter_assoc]
    have Hf := conicZeroProjectiveDesc_first (U).a₁ c hu gc f₁ f₂
    simp only [Category.assoc] at Hf
    rw [Hf]
    have hsq := (coefficientShearAdjacentFirst_isPullback
      hπ d e S r hs hp h3 h4 hr a ha).w
    change b₁ ≫ (J).hom ≫ i = ((ρ₁).hom ≫ p) ≫ L₁ at hsq
    rw [coefficientShearAdjacentConicToNext_def]
    simp only [← Category.assoc]
    rw [show (b₁ ≫ (J).hom) ≫ i = ((ρ₁).hom ≫ p) ≫ L₁ from
      (Category.assoc _ _ _).trans hsq]
    simp only [Category.assoc]
    rw [hg₁]
    change _ = Spec.map (CommRingCat.ofHom
      (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom) ≫
      ProjectiveLine.overlapLeft S ≫ ProjectiveLine.chartScaling S a ≫
      ProjectiveLine.right S ≫ f₁
    rw [ProjectiveLine.scaledReciprocal_overlap_assoc]
    rw [← Category.assoc (ProjectiveLine.chartScaling S a⁻¹),
      ← ProjectiveLine.chartScaling_mul, inv_mul_cancel, ProjectiveLine.chartScaling_one,
      Category.id_comp]
    simp only [← Category.assoc]
    exact congrArg (· ≫ f₁) (ProjectiveLine.overlap_condition S)
  · rw [conicZeroBoundarySecond_parameter_assoc]
    have Hf := conicZeroProjectiveDesc_second (U).a₁ c hu gc f₁ f₂
    simp only [Category.assoc] at Hf
    rw [Hf]
    have hsq := (coefficientShearAdjacentSecond_isPullback
      hπ d e S r hs hp h3 h4 hr a ha).w
    change b₂ ≫ (J).hom ≫ i = ((ρ₂).hom ≫ p) ≫ L₂ at hsq
    rw [coefficientShearAdjacentConicToNext_def]
    simp only [← Category.assoc]
    rw [show (b₂ ≫ (J).hom) ≫ i = ((ρ₂).hom ≫ p) ≫ L₂ from
      (Category.assoc _ _ _).trans hsq]
    simp only [Category.assoc]
    rw [hg₂]
    change _ = Spec.map (CommRingCat.ofHom
      (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) ≫
      ProjectiveLine.overlapLeft S ≫ ProjectiveLine.chartScaling S (-a) ≫
      ProjectiveLine.right S ≫ f₂
    rw [ProjectiveLine.scaledReciprocal_overlap_assoc]
    rw [← Category.assoc (ProjectiveLine.chartScaling S (-a)⁻¹),
      ← ProjectiveLine.chartScaling_mul, inv_mul_cancel, ProjectiveLine.chartScaling_one,
      Category.id_comp]
    simp only [← Category.assoc]
    exact congrArg (· ≫ f₂) (ProjectiveLine.overlap_condition S)

end FLT.Mazur.WeierstrassDividedDepth
