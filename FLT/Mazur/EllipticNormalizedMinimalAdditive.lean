/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdditiveLaterBranches
public import FLT.Mazur.EllipticMinimalDiscriminant
public import FLT.Mazur.EllipticNormalizedDoubleRoot

/-!
# The normalized minimal additive component bound

For a generically elliptic minimal equation over a DVR with every
coefficient in the maximal ideal, the actual rational component quotient
is finite and has order at most four. The proof exhausts the double-root
iteration and excludes integral weighted scaling by minimality.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A normalized minimal additive equation has at most four actual component classes. -/
theorem normalizedMinimalAdditive_components {K : Type*} [Field K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A] (W : WeierstrassCurve A)
    [(W.map (algebraMap A K)).IsElliptic] [IsMinimal A (W.map (algebraMap A K))]
    {π : A} (hπ : π ≠ 0) (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) :
    Finite (EllipticComponentQuotient A W) ∧ Nat.card (EllipticComponentQuotient A W) ≤ 4 := by
  classical
  rcases normalizedAdditive_bound_or_double_or_scaling A W hπ hgen h1 h2 h3 h4 h6 with
    hb | ⟨r, t, _, _, h1', h2', h2'', h3', h4', h6'⟩ | ⟨r, t, _, _, h1', h2', h3', h4', h6'⟩
  · exact hb
  · let C : VariableChange A := .mk 1 r 0 t
    let V := C • W
    have : (V.map (algebraMap A K)).IsElliptic := by
      dsimp only [V]
      rw [← map_variableChange]
      infer_instance
    obtain ⟨hf, hc⟩ := normalizedDoubleRoot_components A V hπ hgen
      h1' h2' h2'' h3' h4' h6'
    let e := integralComponentVariableChange A W C
    refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
    rw [← Nat.card_congr e.toEquiv]
    exact hc
  · let C : VariableChange A := .mk 1 r 0 t
    let V := C • W
    have : (V.map (algebraMap A K)).IsElliptic := by
      dsimp only [V]
      rw [← map_variableChange]
      infer_instance
    exact False.elim (not_isMinimal_of_weighted_depths (K := K) V hπ hgen
      h1' h2' h3' h4' h6' (isMinimal_integral_translation W r t))

end FLT.Mazur
