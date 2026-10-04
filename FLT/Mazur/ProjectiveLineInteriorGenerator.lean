/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalUnitGenerator
public import FLT.Mazur.ProjectiveLineMarkedHZero

/-!
# Interior polynomial sections generate on the Laurent chart

A section with left polynomial X induces an actual invertible section morphism
after pullback to the Laurent overlap. The proof uses the existing divisor
trivialization and retains both geometric pullbacks.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveLineMarkedHZero
open FCurve ProjectiveLineMarkedSectionTransition ProjectiveLineMarkedPullbackCoordinates
open ProjectiveLineMarkedDualCoordinates ProjectiveLineMarkedCharts
variable (K : Type u) [Field K] (a : Kˣ) (m : ℕ)

/-- The left pulled-back divisor line has an actual global trivialization. -/
def leftChartTrivialization :
    (pullback (ProjectiveLine.left K)).obj (line K a m) ≅
      structureModule (ProjectiveLine.chart K) :=
  leftPowerIso K a m ≪≫ trivializationOfTop _
    ((show CartierChart ((chartPoint K (a : K)).ker ^ m) (chartTop K) from
      ⟨equation K (a : K) ^ m, (equation_regular K (a : K)).pow m,
        power_equation K (a : K) m⟩).divisorTrivialization ((effectiveCartier K (a : K)).pow m))

/-- The coordinate X becomes a unit on the actual Laurent overlap. -/
lemma interiorCoordinate_isUnit (s : Γ(line K a m, ⊤))
    (hs : sectionPolynomial K a m s = Polynomial.X) :
    IsUnit ((ProjectiveLine.overlapLeft K).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m
        (pullGlobal (ProjectiveLine.left K) (line K a m) s))) := by
  have he := congrArg (coordinateRing K) hs
  rw [sectionPolynomial, RingEquiv.apply_symm_apply] at he
  rw [he, left_coordinate, Polynomial.toLaurent_X]
  exact (LaurentPolynomial.isUnit_T 1).map (laurentRing K).toRingHom

/-- The genuine interior section trivializes the line after the two chart pullbacks. -/
theorem interiorSection_isIso (s : Γ(line K a m, ⊤))
    (hs : sectionPolynomial K a m s = Polynomial.X) :
    IsIso (globalSectionHom _ (pullGlobal (ProjectiveLine.overlapLeft K)
      ((pullback (ProjectiveLine.left K)).obj (line K a m))
      (pullGlobal (ProjectiveLine.left K) (line K a m) s))) :=
  pullGlobal_isIso_of_unit_coordinate (ProjectiveLine.overlapLeft K) _
    (leftChartTrivialization K a m)
    (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m) _
    (interiorCoordinate_isUnit K a m s hs)

end FLT.Mazur.ProjectiveLineMarkedHZero
