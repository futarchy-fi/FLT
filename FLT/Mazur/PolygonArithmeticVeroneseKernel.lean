/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticVeroneseExactness
public import FLT.Mazur.PolygonArithmeticVeroneseIdeal

/-!
# Exact evaluation kernels of the actual compatible Veronese algebra

Homogeneous projection detects the original finite-support coefficients.
Their compatible divisions assemble with the same finite support, proving
that the whole algebra's stage kernel is its actual parameter-ideal power.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Vanishing of an actual Veronese evaluation implies vanishing of every retained coefficient. -/
theorem compatibleVeroneseEval_coefficient_zero (q : ℕ) (hq : 0 < q) (m d : ℕ)
    (s : CompatibleVeroneseSections A π n h q) (hs : compatibleVeroneseEval A π n h q m s = 0) :
    compatibleDegreeEval A π n h m (q * d) (s d) = 0 := by
  apply Subtype.ext
  have he := congrArg (SectionGradedSum.projectDegree (boundaryLine A π m n h) ⊤ (q * d)) hs
  change SectionGradedSum.projectDegree (boundaryLine A π m n h) ⊤ (q * d)
    (compatibleEval A π n h m (compatibleVeroneseToSections A π n h q s)) = _ at he
  rw [← compatibleEval_project, compatibleVeroneseProject_recompose A π n h q hq,
    map_zero] at he
  exact he

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [NeZero n]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- Finite support is preserved when dividing the actual evaluation kernel. -/
theorem exactVeroneseEval_powerDivision (m : ℕ)
    (s : CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h))
    (hs : compatibleVeroneseEval A π n h (exactVeroneseStep A π hne hgen n h) m s = 0) :
    ∃ t : CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h),
      π ^ (m + 1) • t = s := by
  classical
  have hd (d : ℕ) := (exactVeroneseDegree_kernel A π hne hgen n h d m (s d)).mp
    (compatibleVeroneseEval_coefficient_zero A π n h _ (exactVeroneseStep_pos A π hne hgen n h)
      m d s hs)
  choose t ht using hd
  refine ⟨∑ d ∈ s.support, DirectSum.of _ d (t d), ?_⟩
  rw [Finset.smul_sum]
  calc
    _ = ∑ d ∈ s.support, DirectSum.of _ d (s d) := by
      apply Finset.sum_congr rfl
      intro d _hd
      let l : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d →ₗ[A]
          CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h) :=
        DirectSum.lof A ℕ
          (fun i ↦ ↥(compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) i)) d
      exact (l.map_smul (π ^ (m + 1)) (t d)).symm.trans (congrArg l (ht d))
    _ = s := DirectSum.sum_support_of s

include hne hgen in
/-- The complete original Veronese evaluation kernel is its actual parameter-adic power. -/
theorem exactVeroneseEval_ker (m : ℕ) :
    RingHom.ker (compatibleVeroneseEval A π n h (exactVeroneseStep A π hne hgen n h) m) =
      compatibleVeroneseParameterIdeal A π n h (exactVeroneseStep A π hne hgen n h) ^ (m + 1) := by
  apply le_antisymm _ (compatibleVeroneseParameterIdeal_le_ker A π n h _ m)
  intro s hs
  obtain ⟨t, ht⟩ := exactVeroneseEval_powerDivision A π n h hne hgen m s hs
  rw [compatibleVeroneseParameterIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨t, ?_⟩
  rw [Algebra.smul_def, map_pow] at ht
  exact ht.symm

end FLT.Mazur.PolygonArithmeticStages
