/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineSealedCanonicalRatios

/-!
# Canonical ratios on the right normalization chart

The right affine coordinate uses the reciprocal marking. Its actual section
coordinate divided by (X-a⁻¹)^m computes the canonical ratio at the infinity
endpoint, including after the genuine composite map to the projective line.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineRightCanonicalRatios
open FCurve ProjectiveLineMarkedHZero ProjectiveLineMarkedSectionTransition
open ProjectiveLineMarkedPullbackCoordinates ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedCharts ProjectiveLineCanonicalRatios
variable (K : Type u) [Field K] (a : Kˣ)

/-- The genuine polynomial coordinate of a section on the right affine chart. -/
def sectionPolynomial (m : ℕ) (s : Γ(line K a m, ⊤)) : K[X] :=
  (coordinateRing K).symm (chartSectionsCoordinate K a (ProjectiveLine.right K)
    (↑a⁻¹ : K) (right_ideal K a) m (pullGlobal (ProjectiveLine.right K) (line K a m) s))

/-- The right pulled-back line has its powered Cartier trivialization. -/
def chartTrivialization (m : ℕ) :
    (pullback (ProjectiveLine.right K)).obj (line K a m) ≅
      structureModule (ProjectiveLine.chart K) :=
  rightPowerIso K a m ≪≫ trivializationOfTop _
    ((show CartierChart ((chartPoint K (↑a⁻¹ : K)).ker ^ m) (chartTop K) from
      ⟨equation K (↑a⁻¹ : K) ^ m, (equation_regular K (↑a⁻¹ : K)).pow m,
        power_equation K (↑a⁻¹ : K) m⟩).divisorTrivialization
          ((effectiveCartier K (↑a⁻¹ : K)).pow m))

/-- The canonical coordinate is invertible after removing the reciprocal mark. -/
lemma canonicalCoordinate_isUnit (m : ℕ) :
    IsUnit ((chart K a⁻¹).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.right K) (↑a⁻¹ : K) (right_ideal K a) m
        (pullGlobal (ProjectiveLine.right K) (line K a m)
          (divisorSection ((relativeCartier K a).1.pow m) ⊤)))) := by
  rw [coordinate_canonical]
  change IsUnit ((chart K a⁻¹).appTop
    (coordinateRing K (Polynomial.X - Polynomial.C (↑a⁻¹ : K)) ^ m))
  rw [map_pow, chart_coordinate]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ring K a⁻¹)
    (Polynomial.X - Polynomial.C (↑a⁻¹ : K))).map (coordinates K a⁻¹).toRingHom).pow m

/-- The canonical section generates on the punctured right chart. -/
lemma canonicalSection_isIso (m : ℕ) :
    IsIso (globalSectionHom _ (pullGlobal (chart K a⁻¹) _
      (pullGlobal (ProjectiveLine.right K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)))) :=
  pullGlobal_isIso_of_unit_coordinate (chart K a⁻¹) _ (chartTrivialization K a m)
    (chartSectionsCoordinate K a (ProjectiveLine.right K) (↑a⁻¹ : K) (right_ideal K a) m) _
    (canonicalCoordinate_isUnit K a m)

/-- The actual right ratio is the right polynomial over the reciprocal marked factor. -/
lemma canonical_ratio (m : ℕ) (s : Γ(line K a m, ⊤)) :
    let := canonicalSection_isIso K a m
    sectionRatio _ (pullGlobal (chart K a⁻¹) _
      (pullGlobal (ProjectiveLine.right K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)))
      (pullGlobal (chart K a⁻¹) _ (pullGlobal (ProjectiveLine.right K) (line K a m) s)) =
      coordinates K a⁻¹ (algebraMap K[X] (ring K a⁻¹) (sectionPolynomial K a m s) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (↑a⁻¹ : K)) ^ m) := by
  let := canonicalSection_isIso K a m
  apply sectionRatio_pullGlobal_of_coordinate _ _
    (chartSectionsCoordinate K a (ProjectiveLine.right K) (↑a⁻¹ : K) (right_ideal K a) m)
  rw [coordinate_canonical]
  have hp : chartSectionsCoordinate K a (ProjectiveLine.right K) (↑a⁻¹ : K)
      (right_ideal K a) m (pullGlobal (ProjectiveLine.right K) (line K a m) s) =
      coordinateRing K (sectionPolynomial K a m s) := by
    rw [sectionPolynomial, RingEquiv.apply_symm_apply]
  rw [hp, chart_coordinate]
  change _ * (chart K a⁻¹).appTop
    (coordinateRing K (Polynomial.X - Polynomial.C (↑a⁻¹ : K)) ^ m) = _
  rw [map_pow, chart_coordinate, ← map_pow, ← map_mul]
  congr 1
  rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The right normalization open map with its infinity endpoint retained. -/
irreducible_def toLine : Spec (.of (ring K a⁻¹)) ⟶ ProjectiveLine.scheme K :=
  chart K a⁻¹ ≫ ProjectiveLine.right K

/-- The canonical section generates on the actual right normalization open. -/
lemma toLine_canonical_isIso (m : ℕ) :
    IsIso (globalSectionHom _ (pullGlobal (toLine K a) (line K a m)
      (divisorSection ((relativeCartier K a).1.pow m) ⊤))) := by
  rw [toLine_def]
  let := canonicalSection_isIso K a m
  exact globalSectionHom_isIso_comp_pullGlobal _ _ _ _

/-- The right coordinate formula holds through the sealed normalization map. -/
lemma sealed_canonical_ratio (m : ℕ) (s : Γ(line K a m, ⊤)) :
    let := toLine_canonical_isIso K a m
    pullbackSectionRatio (toLine K a) (line K a m)
      (divisorSection ((relativeCartier K a).1.pow m) ⊤) s =
      coordinates K a⁻¹ (algebraMap K[X] (ring K a⁻¹) (sectionPolynomial K a m s) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (↑a⁻¹ : K)) ^ m) := by
  let := toLine_canonical_isIso K a m
  let := canonicalSection_isIso K a m
  let := globalSectionHom_isIso_comp_pullGlobal (chart K a⁻¹) (ProjectiveLine.right K)
    (line K a m) (divisorSection ((relativeCartier K a).1.pow m) ⊤)
  dsimp only
  rw [pullbackSectionRatio_def]
  exact (sectionRatio_pullGlobal_congr (toLine_def K a) _ _ s).trans
    ((sectionRatio_comp_pullGlobal _ _ _ _ _).trans (canonical_ratio K a m s))

/-- The right section coordinate agrees with the established morphism coordinate. -/
lemma sectionPolynomial_hom (m : ℕ)
    (s : structureModule (ProjectiveLine.scheme K) ⟶ line K a m) :
    sectionPolynomial K a m (s.app ⊤ (1 : Γ(ProjectiveLine.scheme K, ⊤))) =
      rightPolynomial K a m s := by
  apply (coordinateRing K).injective
  rw [sectionPolynomial, RingEquiv.apply_symm_apply]
  exact (polynomial_coordinate K a m _ _ _ s).symm

/-- The right numerator is the weighted reversal of the actual left numerator. -/
lemma sectionPolynomial_coeff (m : ℕ) (s : Γ(line K a m, ⊤))
    (j : ℕ) (hj : j ≤ m) :
    (sectionPolynomial K a m s).coeff j =
      (↑((-a)⁻¹) : K) ^ m * (ProjectiveLineMarkedHZero.sectionPolynomial K a m s).coeff
        (m - j) := by
  rw [← globalSectionHom_top (line K a m) s, sectionPolynomial_hom,
    ProjectiveLineMarkedHZero.sectionPolynomial_hom]
  exact ProjectiveLineMarkedPolynomialBounds.rightPolynomial_coeff K a m _ j hj

end FLT.Mazur.ProjectiveLineRightCanonicalRatios
