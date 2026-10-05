/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticIntegralCuspNormalization
public import FLT.Mazur.EllipticNormalizedMinimalAdditive

/-!
# Rational components of minimal additive equations

Over a DVR with perfect residue field, the additive discriminant and c₄
tests produce an integral cusp normalization. Minimality and the actual
component quotient transport through this change, giving a finite quotient
of order at most four without any assumed classification of components.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A minimal additive equation over a DVR with perfect residue has at most four components. -/
theorem minimalAdditive_components {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    [IsMinimal A (W.map (algebraMap A K))]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A) :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨r, s, t, h1, h2, h3, h4, h6⟩ := exists_integral_cusp_normalization W hΔ hc
  let C : VariableChange A := .mk 1 r s t
  let V := C • W
  have : (V.map (algebraMap A K)).IsElliptic := by
    dsimp only [V]
    rw [← map_variableChange]
    infer_instance
  have : IsMinimal A (V.map (algebraMap A K)) :=
    isMinimal_integral_change_of_u_one W C rfl
  obtain ⟨hf, hb⟩ := normalizedMinimalAdditive_components A V hπ.ne_zero hπ.maximalIdeal_eq
    h1 h2 h3 h4 h6
  let e := integralComponentVariableChange A W C
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  exact hb

end FLT.Mazur
