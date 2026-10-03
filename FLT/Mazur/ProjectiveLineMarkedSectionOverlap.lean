/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRegularity
public import FLT.Mazur.ProjectiveLineMarkedSectionTransition
public import FLT.Mazur.ProjectiveLineMarkedPolynomialReciprocal

/-!
# Compatibility of independently constructed marked sections

The actual sections associated to a bounded polynomial and its reciprocal
agree on the common Laurent overlap. Cancellation takes place on arbitrary
sections of the trivialized overlap module, without assuming a global section.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedSectionOverlap
open FLT.Mazur FCurve ProjectiveLineMarkedSectionTransition
open ProjectiveLineMarkedPullbackCoordinates ProjectiveLineMarkedDualCoordinates
open ProjectiveLineMarkedCharts PolygonDivisorNormalizationPullback
open ProjectiveLineMarkedPolynomialReciprocal
variable (K : Type u) [Field K] (a : Kˣ) (m : ℕ)
/-- Construct the independent left chart section from a polynomial. -/
def leftSection (p : K[X]) : Γ((pullback (ProjectiveLine.left K)).obj (line K a m), ⊤) :=
  (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m).symm
    (coordinateRing K p)
/-- Construct the independent reciprocal chart section from a polynomial. -/
def rightSection (q : K[X]) : Γ((pullback (ProjectiveLine.right K)).obj (line K a m), ⊤) :=
  (chartSectionsCoordinate K a (ProjectiveLine.right K) (a⁻¹ : Kˣ)
    (right_ideal K a) m).symm (coordinateRing K q)
/-- Pull the independent left section to the Laurent overlap. -/
def leftOverlap (p : K[X]) :=
  pullOverlap (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K)
    (line K a m) (leftSection K a m p)
/-- Pull the independent right section to the same Laurent module. -/
def rightOverlap (q : K[X]) :=
  pullOverlapAlong (ProjectiveLine.overlapRight K) (ProjectiveLine.right K)
    (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K)
    (ProjectiveLine.overlap_condition K).symm (line K a m) (rightSection K a m q)
/-- Regular Laurent functions act injectively on all sections of the overlap module. -/
lemma overlap_regular (r : Γ(ProjectiveLine.overlap K, ⊤)) (hr : IsRegular r) :
    IsSMulRegular Γ((pullback (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K)).obj
      (line K a m), ⊤) r := by
  let hU : CartierChart ((chartPoint K (a : K)).ker ^ m) (chartTop K) :=
    ⟨equation K (a : K) ^ m, (equation_regular K (a : K)).pow m,
      power_equation K (a : K) m⟩
  let e := moduleTopTrivialization _
    (hU.divisorTrivialization ((effectiveCartier K (a : K)).pow m))
  exact regular_smul_of_trivialization _
    (((pullbackComp (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K)).app
      (line K a m)).symm ≪≫
      (pullback (ProjectiveLine.overlapLeft K)).mapIso (leftPowerIso K a m ≪≫ e) ≪≫
      modulePullbackUnitIso (ProjectiveLine.overlapLeft K)) r hr
/-- The right canonical coordinate acts injectively on the common overlap module. -/
lemma coordinate_regular :
    IsSMulRegular Γ((pullback (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K)).obj
      (line K a m), ⊤) ((ProjectiveLine.overlapRight K).appTop
        (chartSectionsCoordinate K a (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) m
          (pullGlobal (ProjectiveLine.right K) (line K a m)
            (divisorSection ((relativeCartier K a).1.pow m) ⊤)))) := by
  apply overlap_regular K a m
  rw [coordinate_canonical]
  exact regular_appTop_of_flat (ProjectiveLine.overlapRight K)
    _ ((equation_regular K (a⁻¹ : Kˣ)).pow m)
/-- The two canonical section coordinates have the specified transition. -/
lemma coordinate_transition :
    (ProjectiveLine.overlapRight K).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) m
        (pullGlobal (ProjectiveLine.right K) (line K a m)
          (divisorSection ((relativeCartier K a).1.pow m) ⊤))) =
    laurentRing K ((ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m) *
    (ProjectiveLine.overlapLeft K).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m
        (pullGlobal (ProjectiveLine.left K) (line K a m)
          (divisorSection ((relativeCartier K a).1.pow m) ⊤))) := by
  rw [coordinate_canonical, coordinate_canonical]
  exact canonical_transition K a m
/-- Polynomial compatibility gives compatibility of independent local coordinates. -/
lemma polynomial_transition (p q : K[X])
    (h : LaurentPolynomial.invert (Polynomial.toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m *
        Polynomial.toLaurent p) :
    (ProjectiveLine.overlapRight K).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) m
        (rightSection K a m q)) =
    laurentRing K ((ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m) *
    (ProjectiveLine.overlapLeft K).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m
        (leftSection K a m p)) := by
  rw [rightSection, leftSection, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    right_coordinate, left_coordinate, h, map_mul]
/-- Compatible polynomial coordinates give equal actual overlap sections. -/
theorem overlap_eq (p q : K[X])
    (h : LaurentPolynomial.invert (Polynomial.toLaurent q) =
      (ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m *
        Polynomial.toLaurent p) : leftOverlap K a m p = rightOverlap K a m q := by
  unfold leftOverlap rightOverlap
  refine pullGlobal_local_glue (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K)
    (ProjectiveLine.overlapRight K) (ProjectiveLine.right K)
    (ProjectiveLine.overlap_condition K) (line K a m)
    (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m)
    (chartSectionsCoordinate K a (ProjectiveLine.right K) (a⁻¹ : Kˣ) (right_ideal K a) m)
    (divisorSection ((relativeCartier K a).1.pow m) ⊤)
    (leftSection K a m p) (rightSection K a m q)
    (laurentRing K ((ProjectiveLineMarkedTransition.transition a : K[T;T⁻¹]) ^ m))
    ?_ ?_ ?_
  · exact coordinate_regular K a m
  · exact coordinate_transition K a m
  · exact polynomial_transition K a m p q h
/-- Every bounded polynomial and its reciprocal give matching chart sections. -/
theorem bounded_overlap (p : Polynomial.degreeLT K (m + 1)) :
    leftOverlap K a m p.val = rightOverlap K a m (reciprocal a m p.val) :=
  overlap_eq K a m _ _ (bounded_reciprocal_transition a m p)
end FLT.Mazur.ProjectiveLineMarkedSectionOverlap
