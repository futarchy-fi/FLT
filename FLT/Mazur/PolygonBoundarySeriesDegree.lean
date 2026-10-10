/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryGradedParameter

/-!
# Actual homogeneous section modules over the complete base

Restrict the existing homogeneous modules along the original complete-base
structural scalar maps. Every original adjacent transition is linear over
this one coefficient ring, as required for compatible scalar division.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family boundarySeriesScalars

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- Original power-series coefficients as structural sections of a stage. -/
def boundarySeriesScalarMap (m : ℕ) : PowerSeries R →+* Γ((family R m n h).left, ⊤) :=
  (stageScalars R m n h).comp (seriesToStage R m).toRingHom

/-- The actual structural scalar map agrees with the original graded-ring scalar map. -/
theorem boundarySeriesScalarMap_algebraMap (m : ℕ) (r : PowerSeries R) :
    algebraMap Γ((family R m n h).left, ⊤) (boundaryGradedSections R n h m)
      (boundarySeriesScalarMap R n h m r) = boundarySeriesScalars R n h m r := by
  rw [boundarySeriesScalars_stage]
  rfl

/-- One actual homogeneous module, with scalars restricted from the complete base. -/
def boundarySeriesDegree (m d : ℕ) : ModuleCat (PowerSeries R) :=
  (ModuleCat.restrictScalars (boundarySeriesScalarMap R n h m)).obj
    (ModuleCat.of Γ((family R m n h).left, ⊤) (grade (boundaryLine R m n h) ⊤ d))

/-- The restricted action is multiplication by the original complete-base scalar. -/
theorem boundarySeriesDegree_smul_val (m d : ℕ) (r : PowerSeries R)
    (s : boundarySeriesDegree R n h m d) :
    (r • s).val = boundarySeriesScalars R n h m r * s.val := by
  change boundarySeriesScalarMap R n h m r • s.val = _
  rw [Algebra.smul_def, boundarySeriesScalarMap_algebraMap]

/-- The original adjacent homogeneous transition is linear over the complete base. -/
def boundarySeriesDegreeTransition (m d : ℕ) :
    boundarySeriesDegree R n h (m + 1) d →ₗ[PowerSeries R]
      boundarySeriesDegree R n h m d where
  toFun s := ⟨boundarySectionsMap R n h (homOfLE (Nat.le_succ m)) s.val,
    boundarySectionsMap_mem_grade R n h (homOfLE (Nat.le_succ m)) s.property⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := by
    apply Subtype.ext
    let t : boundarySeriesDegree R n h m d :=
      ⟨boundarySectionsMap R n h (homOfLE (Nat.le_succ m)) s.val,
        boundarySectionsMap_mem_grade R n h (homOfLE (Nat.le_succ m)) s.property⟩
    change boundarySectionsMap R n h (homOfLE (Nat.le_succ m)) (r • s).val = (r • t).val
    rw [boundarySeriesDegree_smul_val, boundarySeriesDegree_smul_val, map_mul]
    have he := DFunLike.congr_fun (boundarySectionsMap_series R n h
      (homOfLE (Nat.le_succ m))) r
    exact congrArg (fun a ↦ a * boundarySectionsMap R n h
      (homOfLE (Nat.le_succ m)) s.val) he

/-- Powers of the parameter retain their original ring multiplication on homogeneous values. -/
theorem boundarySeriesDegree_parameterPower_val (m d k : ℕ)
    (s : boundarySeriesDegree R n h m d) :
    ((PowerSeries.X : PowerSeries R) ^ k • s).val =
      boundarySeriesScalars R n h m PowerSeries.X ^ k * s.val := by
  rw [boundarySeriesDegree_smul_val, map_pow]

end FLT.Mazur.PolygonInfinitesimalStages
