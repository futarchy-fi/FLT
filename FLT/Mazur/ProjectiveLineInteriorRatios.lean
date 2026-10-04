/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioCoordinates
public import FLT.Mazur.ProjectiveLineInteriorGenerator

/-!
# Laurent ratios of marked projective-line sections

On the torus a section with polynomial X is a generator, and the ratio of any
section to it is its actual polynomial coordinate multiplied by T⁻¹.
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

/-- The actual left coordinate restricts to the Laurent polynomial inclusion. -/
lemma sectionPolynomial_laurent (s : Γ(line K a m, ⊤)) :
    (ProjectiveLine.overlapLeft K).appTop
      (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m
        (pullGlobal (ProjectiveLine.left K) (line K a m) s)) =
      laurentRing K (Polynomial.toLaurent (sectionPolynomial K a m s)) := by
  rw [sectionPolynomial, ← left_coordinate, RingEquiv.apply_symm_apply]

/-- The genuine ratio after the two chart pullbacks is the Laurent quotient by X. -/
lemma interiorSection_ratio (s t : Γ(line K a m, ⊤))
    (hs : sectionPolynomial K a m s = Polynomial.X) :
    let := interiorSection_isIso K a m s hs
    sectionRatio _
      (pullGlobal (ProjectiveLine.overlapLeft K) _
        (pullGlobal (ProjectiveLine.left K) (line K a m) s))
      (pullGlobal (ProjectiveLine.overlapLeft K) _
        (pullGlobal (ProjectiveLine.left K) (line K a m) t)) =
      laurentRing K (Polynomial.toLaurent (sectionPolynomial K a m t) *
        LaurentPolynomial.T (-1)) := by
  let := interiorSection_isIso K a m s hs
  apply sectionRatio_pullGlobal_of_coordinate _ _
    (chartSectionsCoordinate K a (ProjectiveLine.left K) a (left_ideal K a) m)
  rw [sectionPolynomial_laurent, sectionPolynomial_laurent, hs, Polynomial.toLaurent_X,
    ← map_mul, mul_assoc, ← LaurentPolynomial.T_add]
  simp

/-- The ratio formula retains the actual composite torus-to-projective-line map. -/
lemma interiorSection_ratio_comp (s t : Γ(line K a m, ⊤))
    (hs : sectionPolynomial K a m s = Polynomial.X) :
    let := interiorSection_isIso K a m s hs
    let := globalSectionHom_isIso_comp_pullGlobal
      (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K) (line K a m) s
    sectionRatio _
      (pullGlobal (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) (line K a m) s)
      (pullGlobal (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) (line K a m) t) =
      laurentRing K (Polynomial.toLaurent (sectionPolynomial K a m t) *
        LaurentPolynomial.T (-1)) := by
  let := interiorSection_isIso K a m s hs
  exact (sectionRatio_comp_pullGlobal _ _ _ s t).trans (interiorSection_ratio K a m s t hs)

end FLT.Mazur.ProjectiveLineMarkedHZero
