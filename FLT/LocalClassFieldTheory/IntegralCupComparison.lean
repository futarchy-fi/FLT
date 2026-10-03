/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralCochainCup
public import FLT.LocalClassFieldTheory.IntegralH1Equivalence

/-!
# The explicit cup represents the integral continuous cup

The existing field-valued scalar character cups with coefficient cocycles
inside the Z-linear continuous complex. The operation descends to actual H1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory GaloisRepresentation.Extensions

variable {k G M : Type} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

omit [SMulCommClass G k M] in
/-- The explicit cup is precisely the cup cochain in the integral complex. -/
theorem integralCupOne_explicit (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) :
    integralCupOne (r := ℤ) (continuousOneCochain c.val) d =
      continuousTwoCochain (k := ℤ) (continuousCup c d) := rfl

/-- The explicit cup represents its actual integral cohomology class. -/
theorem integralCupClass_explicit (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) :
    integralCupClass (r := ℤ) c d =
      integralH2Class (k := ℤ) (continuousCup c d) (continuousCup_isCocycle c d) := rfl

/-- Integral cup vanishing is exactly an actual continuous coboundary witness. -/
theorem integralCupClass_eq_zero (c : ContinuousCocycle G M) (d : ContinuousAddCharacter G k) :
    integralCupClass (r := ℤ) c d = 0 ↔ ContinuousIsCoboundaryTwo (continuousCup c d) :=
  integralH2Class_eq_zero (continuousCup c d) (continuousCup_isCocycle c d)

/-- Changing the splitting leaves the integral cup class unchanged. -/
theorem integralCupClass_splitting (c c' : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k)
    (h : SplittingEquivalent (fun g => c.val g) (fun g => c'.val g)) :
    integralCupClass (r := ℤ) c' d = integralCupClass (r := ℤ) c d := by
  obtain ⟨a, ha⟩ := h
  let K := continuousCochains ℤ G M
  let z := integralCupOne (r := ℤ) (continuousOneCochain c.val) d
  let z' := integralCupOne (r := ℤ) (continuousOneCochain c'.val) d
  have hz : (K.d 2 ((ComplexShape.up ℕ).next 2)).hom z = 0 := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
    exact integralCupOne_cycle (r := ℤ) _
      ((continuousOneCochain_cycle_iff (k := ℤ) _).mpr c.property) d
  have hz' : (K.d 2 ((ComplexShape.up ℕ).next 2)).hom z' = 0 := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
    exact integralCupOne_cycle (r := ℤ) _
      ((continuousOneCochain_cycle_iff (k := ℤ) _).mpr c'.property) d
  have hd : (K.d 2 ((ComplexShape.up ℕ).next 2)).hom (z' - z) = 0 := by
    rw [map_sub, hz, hz', sub_self]
  rw [← sub_eq_zero]
  change cochainHomologyClass K 2 z' hz' - cochainHomologyClass K 2 z hz = 0
  rw [← cochainHomologyClass_sub K 2 z' z hz' hz hd, cochainHomologyClass_eq_zero_iff]
  rw [(ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)]
  refine ⟨continuousOneCochain (k := ℤ) (splittingCupCochain d a), ?_⟩
  apply Subtype.ext
  funext x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, continuous_d_one]
  exact continuousCup_splitting_difference c c' d a ha (x 0) (x 1)

/-- Right cup with a scalar character, defined on actual integral H1. -/
def integralCohomologyCup (x : continuousCohomology ℤ G M 1)
    (d : ContinuousAddCharacter G k) : continuousCohomology ℤ G M 2 :=
  Quotient.lift (fun c => integralCupClass (r := ℤ) c d)
    (fun c c' h => (integralCupClass_splitting c c' d h).symm)
    ((integralH1Equiv (k := ℤ)).symm x)

/-- On a representative the descended integral cup has the explicit low-degree formula. -/
theorem integralCohomologyCup_class (c : ContinuousCocycle G M)
    (d : ContinuousAddCharacter G k) :
    integralCohomologyCup (integralH1Class (k := ℤ) c) d =
      integralH2Class (k := ℤ) (continuousCup c d) (continuousCup_isCocycle c d) := by
  unfold integralCohomologyCup
  change Quotient.lift _ _ ((integralH1Equiv (k := ℤ)).symm
    (integralH1Equiv (continuousClassMk c))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end LocalClassFieldTheory
