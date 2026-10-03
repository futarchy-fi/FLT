/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCharacteristicZeroCohomology

/-!
# Integral cohomology of rational coefficient modules

The inhomogeneous differential is independent of the scalar ring. A continuous
rational bounding cochain therefore also bounds in the integral complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory Limits groupCohomology

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℚ M]
  [DistribMulAction G M] [SMulCommClass G ℚ M]

/-- Changing scalars from Q to Z does not change the actual differential. -/
theorem rationalIntegral_d (n : ℕ) (c : (Fin n → G) → M) :
    (inhomogeneousCochains.d (Rep.of (Representation.ofDistribMulAction ℚ G M)) n).hom c =
      (inhomogeneousCochains.d (Rep.of (Representation.ofDistribMulAction ℤ G M)) n).hom c := by
  funext x
  simp only [inhomogeneousCochains.d_hom_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (-1 : ℚ) ^ (i.val + 1) = (((-1 : ℤ) ^ (i.val + 1) : ℤ) : ℚ) by norm_cast,
    Int.cast_smul_eq_zsmul]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M]

/-- Every positive integral cocycle with rational coefficients bounds continuously. -/
theorem integralRational_cycle_bounds (n : ℕ) (c : (continuousCochains ℤ G M).X (n + 1))
    (hc : ((continuousCochains ℤ G M).d (n + 1) (n + 2)).hom c = 0) :
    ∃ b : (continuousCochains ℤ G M).X n,
      ((continuousCochains ℤ G M).d n (n + 1)).hom b = c := by
  let q : (continuousCochains ℚ G M).X (n + 1) := ⟨c.val, c.property⟩
  have hq : ((continuousCochains ℚ G M).d (n + 1) (n + 2)).hom q = 0 := by
    apply Subtype.ext
    have he := congrArg Subtype.val hc
    simp [continuousCochains, CochainComplex.of.d, continuousCochainD] at he ⊢
    simpa using (rationalIntegral_d (n + 1) c.val).trans he
  have hqn : ((continuousCochains ℚ G M).d (n + 1)
      ((ComplexShape.up ℕ).next (n + 1))).hom q = 0 := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl)]
    exact hq
  have hz := continuousCharacteristicZero_cohomology_eq_zero ℚ G M n
    (cochainHomologyClass (continuousCochains ℚ G M) (n + 1) q hqn)
  have hbex := (cochainHomologyClass_eq_zero_iff _ _ _ _).mp hz
  rw [(ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at hbex
  obtain ⟨b, hb⟩ := hbex
  refine ⟨⟨b.val, b.property⟩, ?_⟩
  apply Subtype.ext
  have he := congrArg Subtype.val hb
  simp [continuousCochains, CochainComplex.of.d, continuousCochainD] at he ⊢
  simpa using (rationalIntegral_d n b.val).symm.trans he

/-- Positive integral continuous cohomology of a rational module is zero. -/
theorem integralRational_cohomology_isZero (n : ℕ) :
    IsZero ((continuousCochains ℤ G M).homology (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices ∀ x : (continuousCochains ℤ G M).homology (n + 1), x = 0 from
    ⟨fun x y => (this x).trans (this y).symm⟩
  intro x
  obtain ⟨c, hc, rfl⟩ := cochainHomologyClass_surjective (continuousCochains ℤ G M) (n + 1) x
  apply (cochainHomologyClass_eq_zero_iff _ _ _ _).mpr
  rw [(ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
  apply integralRational_cycle_bounds n c
  rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl)] at hc
  exact hc

end LocalClassFieldTheory
