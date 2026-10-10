/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleVeronese
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The internal grading of the original compatible Veronese algebra

The external direct sum has its canonical internal grading by the images
of its homogeneous insertions. The decomposition and multiplication retain
the original compatible sections, so this is the grading used for Proj.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- The original retained degree as an internal submodule of the compatible Veronese algebra. -/
def compatibleVeroneseGrade (d : ℕ) :
    Submodule (PowerSeries R) (CompatibleVeroneseSections R n h q) :=
  LinearMap.range (DirectSum.lof (PowerSeries R) ℕ
    (fun i ↦ ↥(compatibleVeroneseDegree R n h q i)) d)

/-- Insert each original component into its internal homogeneous submodule. -/
def compatibleVeroneseDecomposition : CompatibleVeroneseSections R n h q →ₗ[PowerSeries R]
    ⨁ d : ℕ, compatibleVeroneseGrade R n h q d :=
  DirectSum.toModule (PowerSeries R) ℕ _ (fun d ↦
    (DirectSum.lof (PowerSeries R) ℕ (fun d ↦ compatibleVeroneseGrade R n h q d) d).comp
      (DirectSum.lof (PowerSeries R) ℕ
        (fun i ↦ ↥(compatibleVeroneseDegree R n h q i)) d).rangeRestrict)

/-- The canonical decomposition keeps the original homogeneous insertion. -/
theorem compatibleVeroneseDecomposition_of (d : ℕ)
    (s : compatibleVeroneseDegree R n h q d) :
    compatibleVeroneseDecomposition R n h q (DirectSum.of _ d s) =
      DirectSum.of _ d ⟨DirectSum.of _ d s, ⟨s, rfl⟩⟩ := by
  unfold compatibleVeroneseDecomposition
  conv_lhs => rw [← DirectSum.lof_eq_of (R := PowerSeries R)]
  rw [DirectSum.toModule_lof]
  rfl

/-- Recomposition recovers every original compatible Veronese section. -/
theorem compatibleVeronese_recompose_decomposition :
    (DirectSum.coeLinearMap (compatibleVeroneseGrade R n h q)).comp
      (compatibleVeroneseDecomposition R n h q) = LinearMap.id := by
  ext d s : 2
  change DirectSum.coeLinearMap _
    (compatibleVeroneseDecomposition R n h q (DirectSum.of _ d s)) = _
  rw [compatibleVeroneseDecomposition_of, DirectSum.coeLinearMap_of]
  rfl

/-- Decomposition recovers every internally homogeneous summand. -/
theorem compatibleVeronese_decomposition_recompose :
    (compatibleVeroneseDecomposition R n h q).comp
      (DirectSum.coeLinearMap (compatibleVeroneseGrade R n h q)) = LinearMap.id := by
  ext d s : 2
  rcases s with ⟨s, ⟨t, rfl⟩⟩
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.coeLinearMap_of,
    LinearMap.id_apply]
  exact compatibleVeroneseDecomposition_of R n h q d t

/-- The internal compatible homogeneous modules decompose the actual Veronese algebra. -/
instance compatibleVeroneseGradeDecomposition :
    DirectSum.Decomposition (compatibleVeroneseGrade R n h q) :=
  DirectSum.Decomposition.ofLinearMap _ (compatibleVeroneseDecomposition R n h q)
    (compatibleVeronese_recompose_decomposition R n h q)
    (compatibleVeronese_decomposition_recompose R n h q)

/-- The original unit and section multiplication respect the internal Veronese grading. -/
instance compatibleVeroneseGradeGradedAlgebra :
    GradedAlgebra (compatibleVeroneseGrade R n h q) where
  __ := compatibleVeroneseGradeDecomposition R n h q
  one_mem := ⟨GradedMonoid.GOne.one
    (A := fun d ↦ ↥(compatibleVeroneseDegree R n h q d)), rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨GradedMonoid.GMul.mul
      (A := fun d ↦ ↥(compatibleVeroneseDegree R n h q d)) s t,
      (DirectSum.of_mul_of
        (A := fun d ↦ ↥(compatibleVeroneseDegree R n h q d)) s t).symm⟩

end FLT.Mazur.PolygonInfinitesimalStages
