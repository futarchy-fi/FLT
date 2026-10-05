/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodalDiscriminantDepth
public import FLT.Mazur.EllipticNonsplitNodeBound
public import FLT.Mazur.EllipticSplitNodeComponents
public import FLT.Mazur.NodeNonsplitTangent

/-!
# Nonsplit nodal components without a supplied depth model

An arbitrary nonsplit nodal equation over a DVR with perfect residue field
has a finite discriminant depth. Integral translations supply the required
coefficient depths and preserve nonsplitting. The resulting bound on the
actual component quotient transports back to the original equation.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A nonsplit node admits the coefficient model and irreducible tangent at finite depth. -/
theorem exists_nonsplitNodeDepth_model {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄)
    (hns : ¬ (W.nodePoly.map (residue A)).Splits) :
    ∃ n : ℕ, 0 < n ∧ W.Δ ∈ maximalIdeal A ^ n ∧ W.Δ ∉ maximalIdeal A ^ (n + 1) ∧
      ∃ π r t : A, π ≠ 0 ∧ maximalIdeal A = Ideal.span {π} ∧
        let V := VariableChange.mk 1 r 0 t • W
        Irreducible ((nodeTangentPolynomial V).map (residue A)) ∧ IsUnit V.b₂ ∧
          V.a₃ ∈ maximalIdeal A ^ (n + 1) ∧ V.a₄ ∈ maximalIdeal A ^ (n + 1) ∧
            V.a₆ ∈ maximalIdeal A ^ n ∧ V.a₆ ∉ maximalIdeal A ^ (n + 1) := by
  have hΔ0 : W.Δ ≠ 0 := by
    intro hz
    apply (W.map (algebraMap A K)).isUnit_Δ.ne_zero
    simp [map_Δ, hz]
  obtain ⟨n, hn, hd, hd'⟩ := exists_positive_maximalIdeal_depth hΔ0 hΔ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨r, t, hb, h3, h4, h6, h6'⟩ := exists_nodal_discriminant_depth W n hn hd hd' hc
  let V := VariableChange.mk 1 r 0 t • W
  have hns' : ¬ (V.map (residue A)).nodePoly.Splits := by
    rw [map_nodePoly]
    exact fun hs => hns ((nodePoly_map_splits_smul_iff (residue A) W _).mp hs)
  have hi := nodeTangentPolynomial_irreducible_of_nonsplit (V.map (residue A))
    ((residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) h3))
    ((residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) h4))
    ((residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) h6)) hns'
  refine ⟨n, hn, hd, hd', π, r, t, hπ.ne_zero, hπ.maximalIdeal_eq, ?_, hb, h3, h4, h6, h6'⟩
  simpa [nodeTangentPolynomial] using hi

/-- An arbitrary nonsplit nodal component quotient is finite, killed by two,
and of order at most two. -/
theorem nonsplitNodal_components {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄)
    (hns : ¬ (W.nodePoly.map (residue A)).Splits) :
    Finite (EllipticComponentQuotient A W) ∧
      (∀ c : EllipticComponentQuotient A W, 2 • c = 0) ∧
      Nat.card (EllipticComponentQuotient A W) ≤ 2 := by
  classical
  obtain ⟨n, hn, _, _, π, r, t, hπ0, hπ, hi, hb, h3, h4, h6, h6'⟩ :=
    exists_nonsplitNodeDepth_model A W hΔ hc hns
  let C : VariableChange A := .mk 1 r 0 t
  have : ((C • W).map (algebraMap A K)).IsElliptic := by
    rw [← map_variableChange]
    infer_instance
  let e := integralComponentVariableChange A W C
  obtain ⟨hf, htwo, hcard⟩ := nonsplitNode_components A (C • W) hi hn hπ0 hπ hb h3 h4 h6 h6'
  let := hf
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_, ?_⟩
  · intro c
    obtain ⟨d, rfl⟩ := e.surjective c
    rw [← map_nsmul, htwo, map_zero]
  · rw [← Nat.card_congr e.toEquiv]
    exact hcard

end FLT.Mazur
