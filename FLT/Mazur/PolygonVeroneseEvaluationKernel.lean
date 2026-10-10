/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseDegreeExactness
public import FLT.Mazur.PolygonVeroneseParameterIdeal

/-!
# Exact evaluation kernels of the actual compatible Veronese algebra

Homogeneous projection detects the original finite-support coefficients.
Their compatible divisions assemble with the same finite support, proving
that the whole algebra's stage kernel is its actual parameter-ideal power.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- Vanishing of an actual Veronese evaluation implies vanishing of every retained coefficient. -/
theorem compatibleVeroneseEval_coefficient_zero (q : ℕ) (hq : 0 < q) (m d : ℕ)
    (s : CompatibleVeroneseSections K n h q) (hs : compatibleVeroneseEval K n h q m s = 0) :
    compatibleDegreeEval K n h m (q * d) (s d) = 0 := by
  apply Subtype.ext
  have he := congrArg (SectionGradedSum.projectDegree (boundaryLine K m n h) ⊤ (q * d)) hs
  change SectionGradedSum.projectDegree (boundaryLine K m n h) ⊤ (q * d)
    (compatibleEval K n h m (compatibleVeroneseToSections K n h q s)) = _ at he
  rw [← compatibleEval_project, compatibleVeroneseProject_recompose K n h q hq,
    map_zero] at he
  exact he

variable [NeZero n]

/-- Finite support is preserved when dividing the actual evaluation kernel. -/
theorem exactVeroneseEval_powerDivision (m : ℕ)
    (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h))
    (hs : compatibleVeroneseEval K n h (exactVeroneseStep K n h) m s = 0) :
    ∃ t : CompatibleVeroneseSections K n h (exactVeroneseStep K n h),
      (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s := by
  classical
  have hd (d : ℕ) := (exactVeroneseDegree_kernel K n h d m (s d)).mp
    (compatibleVeroneseEval_coefficient_zero K n h _ (exactVeroneseStep_pos K n h) m d s hs)
  choose t ht using hd
  refine ⟨∑ d ∈ s.support, DirectSum.of _ d (t d), ?_⟩
  rw [Finset.smul_sum]
  calc
    _ = ∑ d ∈ s.support, DirectSum.of _ d (s d) := by
      apply Finset.sum_congr rfl
      intro d _hd
      let l : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d →ₗ[PowerSeries K]
          CompatibleVeroneseSections K n h (exactVeroneseStep K n h) :=
        DirectSum.lof (PowerSeries K) ℕ
          (fun i ↦ ↥(compatibleVeroneseDegree K n h (exactVeroneseStep K n h) i)) d
      exact (l.map_smul (PowerSeries.X ^ (m + 1)) (t d)).symm.trans (congrArg l (ht d))
    _ = s := DirectSum.sum_support_of s

/-- The complete original Veronese evaluation kernel is its actual parameter-adic power. -/
theorem exactVeroneseEval_ker (m : ℕ) :
    RingHom.ker (compatibleVeroneseEval K n h (exactVeroneseStep K n h) m) =
      compatibleVeroneseParameterIdeal K n h (exactVeroneseStep K n h) ^ (m + 1) := by
  apply le_antisymm _ (compatibleVeroneseParameterIdeal_le_ker K n h _ m)
  intro s hs
  obtain ⟨t, ht⟩ := exactVeroneseEval_powerDivision K n h m s hs
  rw [compatibleVeroneseParameterIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨t, ?_⟩
  rw [Algebra.smul_def, map_pow] at ht
  exact ht.symm

end FLT.Mazur.PolygonInfinitesimalStages
