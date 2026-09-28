/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantFiltrationPurity
public import FLT.GroupScheme.DiagonalizablePointPurity
public import FLT.GaloisRepresentation.HardlyRamified.KummerModThreeCyclotomic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Three-torsion in the actual constant-three extension of the cube-root group

The nontrivial quadratic action on the quotient rules out a cyclic group of
order nine. Consequently the prescribed quotient admits an additive section,
without assuming that this section is Galois equivariant.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The mod-three character acts on the actual cube-root point group. -/
theorem muThree_modThreeCyclotomic_smul (σ : Γ) (w : muThree.points) :
    σ • w = (modThreeCyclotomic σ : ZMod 3).val • w := by
  apply diagonalPoints_ext (Multiplicative (ZMod 3))
  intro g
  let φ : ℚ ⊗[ZInvTwo] MonoidAlgebra ZInvTwo (Multiplicative (ZMod 3)) →ₐ[ℚ]
      AlgebraicClosure ℚ := w.toMul
  have hg : g ^ 3 = 1 := by
    change Multiplicative.ofAdd ((3 : ℕ) • g.toAdd) = 1
    rw [show (3 : ℕ) • g.toAdd = 0 by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]]
    rfl
  have hp : (φ (diagonalGenerator (Multiplicative (ZMod 3)) g)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hg, map_one, map_one]
  change σ (φ (diagonalGenerator (Multiplicative (ZMod 3)) g)) =
    diagonalEvaluation (Multiplicative (ZMod 3)) g
      (φ ^ (modThreeCyclotomic σ : ZMod 3).val)
  rw [map_pow]
  exact modThreeCyclotomic_spec σ _ hp

/-- Some rational Galois automorphism acts by negation on every cube-root point. -/
theorem exists_muThree_negation : ∃ σ : Γ, ∀ w : muThree.points, σ • w = -w := by
  have hex : ∃ σ : Γ, modThreeCyclotomic σ ≠ 1 := by
    by_contra h
    apply modThreeCyclotomic_ne_one
    apply MonoidHom.ext
    intro σ
    exact not_exists_not.mp h σ
  obtain ⟨σ, hσ⟩ := hex
  have hval : (modThreeCyclotomic σ : ZMod 3) = 2 := by
    have hn := (modThreeCyclotomic σ).ne_zero
    have ho : (modThreeCyclotomic σ : ZMod 3) ≠ 1 := by
      intro h
      exact hσ (Units.ext h)
    generalize (modThreeCyclotomic σ : ZMod 3) = a at *
    fin_cases a <;> trivial
  refine ⟨σ, fun w ↦ ?_⟩
  rw [muThree_modThreeCyclotomic_smul, hval]
  change (2 : ℕ) • w = -w
  have h := muThree_nsmul w
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul] at h
  exact eq_neg_of_add_eq_zero_left h

namespace FiniteFlatExtension

variable {X : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension constantThree X muThree)

include E in
/-- Every point of the actual middle extension is killed by three. -/
theorem constantThree_muThree_nsmul (x : X.points) : (3 : ℕ) • x = 0 := by
  let i := FiniteFlatObject.pointMap E.inclusion
  let q := FiniteFlatObject.pointMap E.quotient
  have hker (y : X.points) (hy : q y = 0) : (3 : ℕ) • y = 0 := by
    obtain ⟨a, rfl⟩ := (E.pointsExact y).mp hy
    exact (map_nsmul i 3 a).symm.trans (by rw [constantThree_nsmul, map_zero])
  have hq : q ((3 : ℕ) • x) = 0 := by rw [map_nsmul, muThree_nsmul]
  obtain ⟨a, ha⟩ := (E.pointsExact _).mp hq
  obtain ⟨σ, hσ⟩ := exists_muThree_negation
  have hfix : σ • ((3 : ℕ) • x) = (3 : ℕ) • x := by
    rw [← ha, ← map_smul, constantThree_smul]
  have hsum : (3 : ℕ) • (σ • x + x) = 0 :=
    hker _ (by rw [map_add, map_smul, hσ, neg_add_cancel])
  have htwo : (3 : ℕ) • x + (3 : ℕ) • x = 0 := by
    simpa only [nsmul_add, ← smul_comm σ (3 : ℕ), hfix] using hsum
  have hthree := hker _ hq
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul,
    htwo, zero_add] at hthree
  exact hthree

/-- The actual quotient has an additive section; equivariance is not asserted. -/
theorem exists_constantThree_muThree_additiveSection :
    ∃ s : muThree.points →+ X.points,
      ∀ w, FiniteFlatObject.pointMap E.quotient (s w) = w := by
  let moduleX : Module (ZMod 3) X.points := AddCommGroup.zmodModule E.constantThree_muThree_nsmul
  let moduleQ : Module (ZMod 3) muThree.points := AddCommGroup.zmodModule muThree_nsmul
  let q := (FiniteFlatObject.pointMap E.quotient).toAddMonoidHom.toZModLinearMap 3
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr E.pointsSurjective)
  exact ⟨s.toAddMonoidHom, fun w ↦ LinearMap.congr_fun hs w⟩

end FiniteFlatExtension
end ThreeAdicPlan
