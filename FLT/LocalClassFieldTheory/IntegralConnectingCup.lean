/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralCoefficientRestriction

/-!
# Scalar cups commute with the integral connecting map

All cochains here are in the Z-linear complex, while characters may take
values in another scalar ring. Continuous lifts are constructed from exactness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G M P Q : Type} [CommRing k] [Group G] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]


variable (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
    Rep.of (Representation.ofDistribMulAction k G P))
  (ψ : Rep.of (Representation.ofDistribMulAction k G P) ⟶
    Rep.of (Representation.ofDistribMulAction k G Q))
  (h : φ ≫ ψ = 0)
  (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
  (hex : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y)

/-- The actual integral connecting map for a scalar-linear exact coefficient sequence. -/
def integralScalarConnectingMap (n : ℕ) :
    (continuousCochains ℤ G Q).homology n ⟶ (continuousCochains ℤ G M).homology (n + 1) :=
  continuousConnectingMap (integralCoefficientRestriction φ) (integralCoefficientRestriction ψ)
    (integralCoefficientRestriction_comp_zero φ ψ h) hφ hψ hex n

/-- Construct representatives of the boundary and its scalar cup in the integral complex. -/
theorem integralScalarConnectingMap_cup_exists
    (c : (continuousCochains ℤ G Q).X 1)
    (hc : ((continuousCochains ℤ G Q).d 1 2).hom c = 0)
    (d : ContinuousScalarCharacter G k) :
    ∃ (a : (continuousCochains ℤ G M).X 2)
      (ha : ((continuousCochains ℤ G M).d 2 3).hom a = 0)
      (hau : ((continuousCochains ℤ G M).d 3 4).hom (integralCupTwo a d) = 0),
      (integralScalarConnectingMap φ ψ h hφ hψ hex 1).hom
          (cochainHomologyClass (continuousCochains ℤ G Q) 1 c (by
            rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)]
            exact hc)) =
        cochainHomologyClass (continuousCochains ℤ G M) 2 a (by
          rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
          exact ha) ∧
      (integralScalarConnectingMap φ ψ h hφ hψ hex 2).hom
          (cochainHomologyClass (continuousCochains ℤ G Q) 2 (integralCupOne c d) (by
            rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
            exact integralCupOne_cycle c hc d)) =
        cochainHomologyClass (continuousCochains ℤ G M) 3 (integralCupTwo a d) (by
          rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 3 4 from rfl)]
          exact hau) := by
  let φZ := integralCoefficientRestriction φ
  let ψZ := integralCoefficientRestriction ψ
  obtain ⟨b, a, hb, ha⟩ := continuousConnectingMap_lift φZ ψZ hψ hex 1 c hc
  have hcup : ((continuousCoefficientMap φZ).f 3).hom (integralCupTwo a d) =
      ((continuousCochains ℤ G P).d 2 3).hom (integralCupOne b d) := by
    rw [integralCoefficientRestriction_cupTwo, ha, integralCupOne_d]
  refine ⟨a, continuousConnectingMap_cycle φZ hφ 1 b a ha,
    continuousConnectingMap_cycle φZ hφ 2 (integralCupOne b d) (integralCupTwo a d) hcup,
    ?_, ?_⟩
  · exact continuousConnectingMap_apply φZ ψZ
      (integralCoefficientRestriction_comp_zero φ ψ h) hφ hψ hex 1 c hc b hb a ha
  · exact continuousConnectingMap_apply φZ ψZ
      (integralCoefficientRestriction_comp_zero φ ψ h) hφ hψ hex 2 (integralCupOne c d)
      (integralCupOne_cycle c hc d) (integralCupOne b d)
      (by rw [integralCoefficientRestriction_cupOne, hb]) (integralCupTwo a d) hcup

end LocalClassFieldTheory
