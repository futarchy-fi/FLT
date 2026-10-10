/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RationalPrimeTorsionLocalModel
public import FLT.Mazur.EllipticSubgroupGeometricComponent

/-!
# The original rational prime subgroup on actual geometric local fibers

Choose the actual minimal equation with its retained generic variable change.
At two, three, and the bad torsion-prime place, every nonzero member of the
transported original cyclic subgroup lies outside the smooth special-fiber
zero component. This uses the actual integral section and Cartesian fiber,
not an assignment of modular points or a proposed component predicate.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing WeierstrassIntegralChart

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing

/-- Actual semistable local models retain the rational generator and its geometric subgroup test. -/
theorem exists_rational_prime_torsion_geometric_model (q : ℕ) [Fact q.Prime]
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
      ((q = 2 ∨ q = 3 ∨ (q = p ∧ W.Δ ∈ maximalIdeal (padicIntegerSubring q))) →
        ∀ T : AddSubgroup.zmultiples Q,
          Set.range (integralPointClosedFiber (padicIntegerSubring q) W T.val) ⊆
              (integralSmoothOpen (W.map (residue (padicIntegerSubring q)))).ι ''
                connectedComponent
                  (integralSmoothZero (W.map (residue (padicIntegerSubring q)))
                    (closedPoint (ResidueField (padicIntegerSubring q)))) ↔ T = 0) := by
  obtain ⟨W, C, hC, hm, ho, hss, hsmall, hp⟩ :=
    exists_rational_prime_torsion_local_model q E p hp17 P hne hP
  refine ⟨W, C, hC, hm, ho, hss, ?_⟩
  intro hq T
  apply primePointClosedFiber_zero_component_iff (padicIntegerSubring q) W p _ ho
  rcases hq with h2 | h3 | ⟨hqp, hd⟩
  · exact hsmall (Or.inl h2)
  · exact hsmall (Or.inr h3)
  · exact hp hqp hd

end FLT.Mazur
