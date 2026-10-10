/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticPadicPrimeSemistability
public import FLT.Mazur.EllipticPadicPrimeComponents
public import FLT.Mazur.EllipticExtensionPrimeSubgroup

/-!
# Actual minimal local models of the original rational prime point

At every rational prime choose an actual minimal equation and retain its
generic variable change. The original rational point extends and transports
through that exact change with the same prime order. Its local model is
semistable, and at two, three and the bad torsion-prime place the transported
point is outside smooth reduction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing
  padicIntegerSubring_residue_finite

/-- Construct the actual local minimal model and preserve the original rational generator. -/
theorem exists_rational_prime_torsion_local_model (q : ℕ) [Fact q.Prime]
    [DecidableEq ℚ_[q]] (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp17 : 17 ≤ p)
    (P : (E.map (algebraMap ℚ ℚ)).toAffine.Point) (hne : P ≠ 0) (hP : p • P = 0) :
    ∃ (W : WeierstrassCurve (padicIntegerSubring q)) (C : VariableChange ℚ_[q])
      (hC : C • E.map (algebraMap ℚ ℚ_[q]) =
        W.map (algebraMap (padicIntegerSubring q) ℚ_[q])),
      IsMinimal (padicIntegerSubring q)
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])) ∧
      let Q := (Projective.Point.toAffineAddEquiv
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).toProjective).symm
          (ellipticExtensionPointHom E W C hC P)
      addOrderOf Q = p ∧
      ((W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasGoodReduction
          (padicIntegerSubring q) ∨
        (W.map (algebraMap (padicIntegerSubring q) ℚ_[q])).HasMultiplicativeReduction
          (padicIntegerSubring q)) ∧
      ((q = 2 ∨ q = 3) → ¬ SmoothReduction (padicIntegerSubring q) W Q) ∧
      (q = p → W.Δ ∈ maximalIdeal (padicIntegerSubring q) →
        ¬ SmoothReduction (padicIntegerSubring q) W Q) := by
  let A := padicIntegerSubring q
  let V := E.map (algebraMap ℚ ℚ_[q])
  obtain ⟨C, hmin⟩ := V.exists_isMinimal A
  let _ := hmin
  let W := (C • V).integralModel A
  have hw : W.map (algebraMap A ℚ_[q]) = C • V := baseChange_integralModel_eq A (C • V)
  let _ : (W.map (algebraMap A ℚ_[q])).IsElliptic := hw.symm ▸ inferInstance
  let _ : IsMinimal A (W.map (algebraMap A ℚ_[q])) := hw.symm ▸ hmin
  let f := ellipticExtensionPointHom (K := ℚ) E W C hw.symm
  let T := (Projective.Point.toAffineAddEquiv (W.map (algebraMap A ℚ_[q])).toProjective).symm
  let Q := T (f P)
  have ho : addOrderOf Q = p := by
    rw [show Q = T (f P) from rfl, AddEquiv.addOrderOf_eq]
    exact ellipticExtensionPoint_addOrderOf E W C hw.symm P hP hne
  have hn : p • Q = 0 := by
    dsimp only [Q]
    rw [← map_nsmul, ← map_nsmul, hP, map_zero, map_zero]
  have hQ : Q ≠ 0 := by
    intro hz
    have hp1 := (Fact.out : p.Prime).one_lt
    rw [hz, addOrderOf_zero] at ho
    omega
  refine ⟨W, C, hw.symm, inferInstance, ho,
    padic_semistable_of_prime_torsion q W p hp17 Q hQ hn, ?_, ?_⟩
  · intro hq
    exact (padic_prime_torsion_components_small q hq W p hp17 Q hQ hn).2.1
  · intro hqp hd
    have hq17 : 17 ≤ q := hqp.symm ▸ hp17
    have hqn : q • Q = 0 := hqp.symm ▸ hn
    exact (padic_prime_torsion_components_at_prime q hq17 W hd Q hQ hqn).2.1

end FLT.Mazur
