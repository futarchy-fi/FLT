/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTowerAssembly
public import FLT.Mazur.PolygonArithmeticTowerDivision

/-!
# Actual evaluation kernels in sufficiently positive compatible degrees

Compatible scalar division is assembled into the original homogeneous
section module. Thus vanishing on stage m is exactly divisibility by
π^(m+1), with the actual integral-base action and actual stage evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- The actual stage evaluation as an integral-base linear map on one homogeneous degree. -/
def compatibleDegreeEval (m d : ℕ) :
    compatibleSectionDegree A π n h d →ₗ[A] boundaryIntegralDegree A π n h m d where
  toFun s := ⟨compatibleEval A π n h m s.val, s.property m⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := Subtype.ext (by
    let t : boundaryIntegralDegree A π n h m d :=
      ⟨compatibleEval A π n h m s.val, s.property m⟩
    change compatibleEval A π n h m (r • s).val = (r • t).val
    rw [compatibleDegree_eval_smul, boundaryIntegralDegree_smul_val])

/-- Homogeneous linear evaluation retains the specified adjacent transition. -/
theorem compatibleDegreeEval_adjacent (m d : ℕ) (s : compatibleSectionDegree A π n h d) :
    boundaryIntegralDegreeTransition A π n h m d (compatibleDegreeEval A π n h (m + 1) d s) =
      compatibleDegreeEval A π n h m d s :=
  Subtype.ext (DFunLike.congr_fun
    (compatibleEval_transition A π n h (homOfLE (Nat.le_succ m))) s.val)

/-- The parameter power defining a stage kills every homogeneous evaluation there. -/
theorem compatibleDegreeEval_parameterPower (m d : ℕ)
    (s : compatibleSectionDegree A π n h d) :
    compatibleDegreeEval A π n h m d (π ^ (m + 1) • s) = 0 := by
  apply Subtype.ext
  change compatibleEval A π n h m _ = 0
  rw [compatibleDegree_eval_smul]
  have hz : boundaryIntegralScalars A π n h m (π ^ (m + 1)) = 0 := by
    apply boundaryIntegralScalars_vanish
    rw [ideal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hz, zero_mul]

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [NeZero n]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- Actual evaluation kernels in positive enough degrees are exactly parameter-power multiples. -/
theorem compatibleDegree_uniformKernel : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : compatibleSectionDegree A π n h d,
      compatibleDegreeEval A π n h m d s = 0 ↔
        ∃ t : compatibleSectionDegree A π n h d,
          π ^ (m + 1) • t = s := by
  obtain ⟨N, hN⟩ := boundaryIntegralDegree_uniformPowerDivision A π hne n h hgen
  refine ⟨N, fun d hd m s ↦ ⟨?_, ?_⟩⟩
  · intro hz
    obtain ⟨t, ht, he⟩ := hN d hd m (fun a ↦ compatibleDegreeEval A π n h a d s)
      (fun a ↦ compatibleDegreeEval_adjacent A π n h a d s) hz
    refine ⟨compatibleDegreeOfAdjacent A π n h d t ht, ?_⟩
    apply Subtype.ext
    apply compatibleEval_ext A π n h
    intro a
    rw [compatibleDegree_eval_smul, compatibleDegreeOfAdjacent_eval]
    exact (boundaryIntegralDegree_smul_val A π n h a d _ (t a)).symm.trans
      (congrArg Subtype.val (he a))
  · rintro ⟨t, rfl⟩
    exact compatibleDegreeEval_parameterPower A π n h m d t

end FLT.Mazur.PolygonArithmeticStages
