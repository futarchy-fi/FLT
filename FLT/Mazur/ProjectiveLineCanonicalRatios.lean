/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleComparedSectionRatio
public import FLT.Mazur.ProjectiveLineInteriorRatios
public import FLT.Mazur.PrincipalAffineRefinement

/-!
# Canonical-denominator ratios on a punctured normalization chart

On D(X-a), the actual canonical section of the m-th marked divisor line
is a generator. Every actual section has ratio P/(X-a)^m in the localization.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineCanonicalRatios
open FCurve ProjectiveLineMarkedHZero ProjectiveLineMarkedSectionTransition
open ProjectiveLineMarkedPullbackCoordinates ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedCharts
variable (K : Type u) [Field K] (a : Kˣ)

/-- The actual coordinate ring of the left normalization chart minus its marked point. -/
abbrev ring := Localization.Away (Polynomial.X - Polynomial.C (a : K))

/-- The principal inclusion of the normalization chart with the mark removed. -/
def chart : Spec (.of (ring K a)) ⟶ ProjectiveLine.chart K :=
  PrincipalAffineRefinement.inclusion (Polynomial.X - Polynomial.C (a : K))

instance chart_isOpenImmersion : IsOpenImmersion (chart K a) := by
  unfold chart
  infer_instance

/-- Canonical coordinates on the localized affine scheme. -/
def coordinates : ring K a ≃+* Γ(Spec (.of (ring K a)), ⊤) :=
  (Scheme.ΓSpecIso (.of (ring K a))).symm.commRingCatIsoToRingEquiv

/-- The actual structure-sheaf pullback is the localization map. -/
lemma chart_coordinate (P : K[X]) :
    (chart K a).appTop (coordinateRing K P) =
      coordinates K a (algebraMap K[X] (ring K a) P) := by
  exact (congrArg (fun f ↦ f.hom P) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap K[X] (ring K a))))).symm

/-- The pulled-back canonical coordinate is invertible on D(X-a). -/
lemma canonicalCoordinate_isUnit (m : ℕ) :
    IsUnit ((chart K a).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m
        (pullGlobal (ProjectiveLine.left K) (line K a m)
          (divisorSection ((relativeCartier K a).1.pow m) ⊤)))) := by
  rw [coordinate_canonical]
  change IsUnit ((chart K a).appTop (coordinateRing K (Polynomial.X - Polynomial.C (a : K)) ^ m))
  rw [map_pow, chart_coordinate]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := ring K a)
    (Polynomial.X - Polynomial.C (a : K))).map (coordinates K a).toRingHom).pow m

/-- The canonical section actually trivializes the pulled-back divisor line. -/
lemma canonicalSection_isIso (m : ℕ) :
    IsIso (globalSectionHom _ (pullGlobal (chart K a) _
      (pullGlobal (ProjectiveLine.left K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)))) :=
  pullGlobal_isIso_of_unit_coordinate (chart K a) _ (leftChartTrivialization K a m)
    (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m) _
    (canonicalCoordinate_isUnit K a m)

/-- The canonical ratio of an actual section is its polynomial divided by the marked equation. -/
lemma canonical_ratio (m : ℕ) (s : Γ(line K a m, ⊤)) :
    let := canonicalSection_isIso K a m
    sectionRatio _ (pullGlobal (chart K a) _
      (pullGlobal (ProjectiveLine.left K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)))
      (pullGlobal (chart K a) _ (pullGlobal (ProjectiveLine.left K) (line K a m) s)) =
      coordinates K a (algebraMap K[X] (ring K a) (sectionPolynomial K a m s) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a : K)) ^ m) := by
  let := canonicalSection_isIso K a m
  apply sectionRatio_pullGlobal_of_coordinate _ _
    (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m)
  rw [coordinate_canonical]
  have hp : chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m
      (pullGlobal (ProjectiveLine.left K) (line K a m) s) =
      coordinateRing K (sectionPolynomial K a m s) := by
    rw [sectionPolynomial, RingEquiv.apply_symm_apply]
  rw [hp, chart_coordinate]
  change _ * (chart K a).appTop
    (coordinateRing K (Polynomial.X - Polynomial.C (a : K)) ^ m) = _
  rw [map_pow, chart_coordinate, ← map_pow, ← map_mul]
  congr 1
  rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The same formula holds for the genuine composite map into the projective line. -/
lemma canonical_ratio_comp (m : ℕ) (s : Γ(line K a m, ⊤)) :
    let := canonicalSection_isIso K a m
    let := globalSectionHom_isIso_comp_pullGlobal (chart K a) (ProjectiveLine.left K)
      (line K a m) (divisorSection ((relativeCartier K a).1.pow m) ⊤)
    sectionRatio _ (pullGlobal (chart K a ≫ ProjectiveLine.left K) (line K a m)
      (divisorSection ((relativeCartier K a).1.pow m) ⊤))
      (pullGlobal (chart K a ≫ ProjectiveLine.left K) (line K a m) s) =
      coordinates K a (algebraMap K[X] (ring K a) (sectionPolynomial K a m s) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a : K)) ^ m) := by
  let := canonicalSection_isIso K a m
  exact (sectionRatio_comp_pullGlobal _ _ _ _ _).trans (canonical_ratio K a m s)

/-- The actual normalization open map, sealed before polygon specialization. -/
irreducible_def toLine : Spec (.of (ring K a)) ⟶ ProjectiveLine.scheme K :=
  chart K a ≫ ProjectiveLine.left K

/-- The canonical generator property on the sealed normalization open. -/
lemma toLine_canonical_isIso (m : ℕ) :
    IsIso (globalSectionHom _ (pullGlobal (toLine K a) (line K a m)
      (divisorSection ((relativeCartier K a).1.pow m) ⊤))) := by
  rw [toLine_def]
  let := canonicalSection_isIso K a m
  exact globalSectionHom_isIso_comp_pullGlobal _ _ _ _

/-- Canonical ratios retain the polynomial formula through the sealed open map. -/
lemma toLine_canonical_ratio (m : ℕ) (s : Γ(line K a m, ⊤)) :
    let := toLine_canonical_isIso K a m
    sectionRatio _ (pullGlobal (toLine K a) (line K a m)
      (divisorSection ((relativeCartier K a).1.pow m) ⊤))
      (pullGlobal (toLine K a) (line K a m) s) =
      coordinates K a (algebraMap K[X] (ring K a) (sectionPolynomial K a m s) *
        IsLocalization.Away.invSelf (Polynomial.X - Polynomial.C (a : K)) ^ m) := by
  let := toLine_canonical_isIso K a m
  let := canonicalSection_isIso K a m
  let := globalSectionHom_isIso_comp_pullGlobal (chart K a) (ProjectiveLine.left K)
    (line K a m) (divisorSection ((relativeCartier K a).1.pow m) ⊤)
  exact (sectionRatio_pullGlobal_congr (toLine_def K a) _ _ s).trans
    (canonical_ratio_comp K a m s)

end FLT.Mazur.ProjectiveLineCanonicalRatios
