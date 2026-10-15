/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticDegreeProjection

/-!
# Actual reduction maps from the compatible section algebra

Stage evaluation factors through the prescribed parameter-adic quotient of
the constructed algebra. Surjectivity and identification with the stage ring
require further lifting theorems and are not assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Original-base scalars act through the actual truncated coefficient algebra at every stage. -/
theorem boundaryIntegralScalars_stage (m : ℕ) (r : A) :
    boundaryIntegralScalars A π n h m r = of (boundaryLine A π m n h) ⊤ 0
      ((family A π m n h).hom.appTop
        ((Scheme.ΓSpecIso (.of (Quotient A π m))).inv
          (Ideal.Quotient.mk (ideal A π ^ (m + 1)) r))) := by
  rw [boundaryIntegralScalars_eq, Scheme.Hom.comp_appTop]
  change of (boundaryLine A π m n h) ⊤ 0
    ((family A π m n h).hom.appTop
      ((baseToIntegral A π m).appTop ((Scheme.ΓSpecIso (.of A)).inv r))) = _
  apply congrArg (of (boundaryLine A π m n h) ⊤ 0)
  apply congrArg ((family A π m n h).hom.appTop)
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (Ideal.Quotient.mk (ideal A π ^ (m + 1))))) r).symm

/-- The exact coefficient ideal of a stage acts by zero in its boundary section ring. -/
theorem boundaryIntegralScalars_vanish (m : ℕ) (r : A)
    (hr : r ∈ ideal A π ^ (m + 1)) : boundaryIntegralScalars A π n h m r = 0 := by
  have hz : Ideal.Quotient.mk (ideal A π ^ (m + 1)) r = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [boundaryIntegralScalars_stage, hz, map_zero, map_zero, map_zero]

/-- Recomposition preserves the integral-base algebra map. -/
theorem compatibleGradedToSections_algebraMap (r : A) :
    compatibleGradedToSections A π n h
      (algebraMap A (CompatibleGradedSections A π n h) r) =
        algebraMap A (CompatibleSections A π n h) r :=
  (DirectSum.coeAlgHom (compatibleSectionDegree A π n h)).commutes r

/-- Stage evaluation retains the actual integral action on the degreewise algebra. -/
theorem compatibleGradedEval_algebraMap (m : ℕ) (r : A) :
    compatibleGradedEval A π n h m
      (algebraMap A (CompatibleGradedSections A π n h) r) =
        boundaryIntegralScalars A π n h m r := by
  change compatibleEval A π n h m (compatibleGradedToSections A π n h _) = _
  rw [compatibleGradedToSections_algebraMap, compatibleEval_algebraMap]

/-- The compatible parameter ideal comes from the original integral base. -/
def compatibleParameterIdeal : Ideal (CompatibleGradedSections A π n h) :=
  Ideal.span {algebraMap A (CompatibleGradedSections A π n h) π}

/-- Evaluation at stage m kills the (m+1)-st power of the actual parameter ideal. -/
theorem compatibleParameterIdeal_le_ker (m : ℕ) :
    compatibleParameterIdeal A π n h ^ (m + 1) ≤
      RingHom.ker (compatibleGradedEval A π n h m) := by
  rw [compatibleParameterIdeal, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  change compatibleGradedEval A π n h m
    ((algebraMap A (CompatibleGradedSections A π n h) π) ^ (m + 1)) = 0
  rw [← map_pow, compatibleGradedEval_algebraMap]
  apply boundaryIntegralScalars_vanish
  rw [ideal, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The constructed parameter-adic quotient maps to the original stage section ring. -/
def compatibleGradedReduction (m : ℕ) :
    (CompatibleGradedSections A π n h ⧸ compatibleParameterIdeal A π n h ^ (m + 1)) →+*
      boundaryGradedSections A π n h m :=
  Ideal.Quotient.lift _ (compatibleGradedEval A π n h m) (compatibleParameterIdeal_le_ker A π n h m)

/-- The reduction map is induced by the actual stage evaluation, with no new choices. -/
theorem compatibleGradedReduction_mk (m : ℕ) (s : CompatibleGradedSections A π n h) :
    compatibleGradedReduction A π n h m (Ideal.Quotient.mk _ s) =
      compatibleGradedEval A π n h m s := rfl

end FLT.Mazur.PolygonArithmeticStages
