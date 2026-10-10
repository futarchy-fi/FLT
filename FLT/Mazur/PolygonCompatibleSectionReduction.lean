/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleDegreeProjection

/-!
# Actual reduction maps from the compatible section algebra

Stage evaluation factors through the prescribed parameter-adic quotient of
the constructed algebra. Surjectivity and identification with the stage ring
require further lifting theorems and are not assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- Complete-base scalars act through the actual truncated coefficient algebra at every stage. -/
theorem boundarySeriesScalars_stage (m : ℕ) (r : PowerSeries R) :
    boundarySeriesScalars R n h m r = of (boundaryLine R m n h) ⊤ 0
      ((family R m n h).hom.appTop
        ((Scheme.ΓSpecIso (.of (Ring R m))).inv (seriesToStage R m r))) := by
  rw [boundarySeriesScalars_eq, Scheme.Hom.comp_appTop]
  change of (boundaryLine R m n h) ⊤ 0
    ((family R m n h).hom.appTop
      ((baseToSeries R m).appTop ((Scheme.ΓSpecIso (.of (PowerSeries R))).inv r))) = _
  apply congrArg (of (boundaryLine R m n h) ⊤ 0)
  apply congrArg ((family R m n h).hom.appTop)
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (seriesToStage R m).toRingHom)) r).symm

/-- The exact coefficient ideal of a stage acts by zero in its boundary section ring. -/
theorem boundarySeriesScalars_vanish (m : ℕ) (r : PowerSeries R)
    (hr : r ∈ parameterIdeal R ^ (m + 1)) : boundarySeriesScalars R n h m r = 0 := by
  have hz : seriesToStage R m r = 0 := by
    change r ∈ RingHom.ker (seriesToStage R m).toRingHom
    rw [seriesToStage_ker]
    exact hr
  rw [boundarySeriesScalars_stage, hz, map_zero, map_zero, map_zero]

/-- Recomposition preserves the complete-base algebra map. -/
theorem compatibleGradedToSections_algebraMap (r : PowerSeries R) :
    compatibleGradedToSections R n h
      (algebraMap (PowerSeries R) (CompatibleGradedSections R n h) r) =
        algebraMap (PowerSeries R) (CompatibleSections R n h) r :=
  (DirectSum.coeAlgHom (compatibleSectionDegree R n h)).commutes r

/-- Stage evaluation retains the actual power-series action on the degreewise algebra. -/
theorem compatibleGradedEval_algebraMap (m : ℕ) (r : PowerSeries R) :
    compatibleGradedEval R n h m
      (algebraMap (PowerSeries R) (CompatibleGradedSections R n h) r) =
        boundarySeriesScalars R n h m r := by
  change compatibleEval R n h m (compatibleGradedToSections R n h _) = _
  rw [compatibleGradedToSections_algebraMap, compatibleEval_algebraMap]

/-- The parameter ideal in the degreewise compatible algebra comes from the complete base. -/
def compatibleParameterIdeal : Ideal (CompatibleGradedSections R n h) :=
  Ideal.span {algebraMap (PowerSeries R) (CompatibleGradedSections R n h) PowerSeries.X}

/-- Evaluation at stage m kills the (m+1)-st power of the actual parameter ideal. -/
theorem compatibleParameterIdeal_le_ker (m : ℕ) :
    compatibleParameterIdeal R n h ^ (m + 1) ≤
      RingHom.ker (compatibleGradedEval R n h m) := by
  rw [compatibleParameterIdeal, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  change compatibleGradedEval R n h m
    ((algebraMap (PowerSeries R) (CompatibleGradedSections R n h) PowerSeries.X) ^ (m + 1)) = 0
  rw [← map_pow, compatibleGradedEval_algebraMap]
  apply boundarySeriesScalars_vanish
  rw [parameterIdeal, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The constructed parameter-adic quotient maps to the original stage section ring. -/
def compatibleGradedReduction (m : ℕ) :
    (CompatibleGradedSections R n h ⧸ compatibleParameterIdeal R n h ^ (m + 1)) →+*
      boundaryGradedSections R n h m :=
  Ideal.Quotient.lift _ (compatibleGradedEval R n h m) (compatibleParameterIdeal_le_ker R n h m)

/-- The reduction map is induced by the actual stage evaluation, with no new choices. -/
theorem compatibleGradedReduction_mk (m : ℕ) (s : CompatibleGradedSections R n h) :
    compatibleGradedReduction R n h m (Ideal.Quotient.mk _ s) =
      compatibleGradedEval R n h m s := rfl

end FLT.Mazur.PolygonInfinitesimalStages
