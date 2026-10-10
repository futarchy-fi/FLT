/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSeriesTowerAssembly
public import FLT.Mazur.PolygonSeriesTowerDivision

/-!
# Actual evaluation kernels in sufficiently positive compatible degrees

Compatible scalar division is assembled into the original homogeneous
section module. Thus vanishing on stage m is exactly divisibility by
X^(m+1), with the actual complete-base action and actual stage evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundarySeriesScalars

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- The actual stage evaluation as a complete-base linear map on one homogeneous degree. -/
def compatibleDegreeEval (m d : ℕ) :
    compatibleSectionDegree R n h d →ₗ[PowerSeries R] boundarySeriesDegree R n h m d where
  toFun s := ⟨compatibleEval R n h m s.val, s.property m⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := Subtype.ext (by
    let t : boundarySeriesDegree R n h m d :=
      ⟨compatibleEval R n h m s.val, s.property m⟩
    change compatibleEval R n h m (r • s).val = (r • t).val
    rw [compatibleDegree_eval_smul, boundarySeriesDegree_smul_val])

/-- Homogeneous linear evaluation retains the specified adjacent transition. -/
theorem compatibleDegreeEval_adjacent (m d : ℕ) (s : compatibleSectionDegree R n h d) :
    boundarySeriesDegreeTransition R n h m d (compatibleDegreeEval R n h (m + 1) d s) =
      compatibleDegreeEval R n h m d s :=
  Subtype.ext (DFunLike.congr_fun
    (compatibleEval_transition R n h (homOfLE (Nat.le_succ m))) s.val)

/-- The parameter power defining a stage kills every homogeneous evaluation there. -/
theorem compatibleDegreeEval_parameterPower (m d : ℕ)
    (s : compatibleSectionDegree R n h d) :
    compatibleDegreeEval R n h m d ((PowerSeries.X : PowerSeries R) ^ (m + 1) • s) = 0 := by
  apply Subtype.ext
  change compatibleEval R n h m _ = 0
  rw [compatibleDegree_eval_smul]
  have hz : boundarySeriesScalars R n h m (PowerSeries.X ^ (m + 1)) = 0 := by
    apply boundarySeriesScalars_vanish
    rw [parameterIdeal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hz, zero_mul]

variable (K : Type) [Field K] [NeZero n]

/-- Actual evaluation kernels in positive enough degrees are exactly parameter-power multiples. -/
theorem compatibleDegree_uniformKernel : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : compatibleSectionDegree K n h d,
      compatibleDegreeEval K n h m d s = 0 ↔
        ∃ t : compatibleSectionDegree K n h d,
          (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s := by
  obtain ⟨N, hN⟩ := boundarySeriesDegree_uniformPowerDivision K n h
  refine ⟨N, fun d hd m s ↦ ⟨?_, ?_⟩⟩
  · intro hz
    obtain ⟨t, ht, he⟩ := hN d hd m (fun a ↦ compatibleDegreeEval K n h a d s)
      (fun a ↦ compatibleDegreeEval_adjacent K n h a d s) hz
    refine ⟨compatibleDegreeOfAdjacent K n h d t ht, ?_⟩
    apply Subtype.ext
    apply compatibleEval_ext K n h
    intro a
    rw [compatibleDegree_eval_smul, compatibleDegreeOfAdjacent_eval]
    exact (boundarySeriesDegree_smul_val K n h a d _ (t a)).symm.trans
      (congrArg Subtype.val (he a))
  · rintro ⟨t, rfl⟩
    exact compatibleDegreeEval_parameterPower K n h m d t

end FLT.Mazur.PolygonInfinitesimalStages
