/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralCochainCup
public import FLT.LocalClassFieldTheory.ContinuousConnectingMap

/-!
# Low-degree cup compatibility with the connecting map

Cup a chosen lift with the same scalar character. Its differential is the
cup of the lifted differential, so the actual boundary has positive sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G M P Q : Type u} [CommRing k] [Group G] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]


/-- Mapping coefficients commutes with the degree-one cup cochain. -/
theorem integralCupOne_coefficient
    (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
      Rep.of (Representation.ofDistribMulAction k G P))
    (c : (continuousCochains k G M).X 1) (d : ContinuousScalarCharacter G k) :
    ((continuousCoefficientMap φ).f 2).hom (integralCupOne c d) =
      integralCupOne (((continuousCoefficientMap φ).f 1).hom c) d := by
  apply Subtype.ext
  funext x
  exact φ.hom.toLinearMap.map_smul (d.val (x 1)) (c.val (fun _ => x 0))

/-- Mapping coefficients commutes with the degree-two cup cochain. -/
theorem integralCupTwo_coefficient
    (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
      Rep.of (Representation.ofDistribMulAction k G P))
    (c : (continuousCochains k G M).X 2) (d : ContinuousScalarCharacter G k) :
    ((continuousCoefficientMap φ).f 3).hom (integralCupTwo c d) =
      integralCupTwo (((continuousCoefficientMap φ).f 2).hom c) d := by
  apply Subtype.ext
  funext x
  exact φ.hom.toLinearMap.map_smul (d.val (x 2)) (c.val ![x 0, x 1])

variable (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
    Rep.of (Representation.ofDistribMulAction k G P))
  (ψ : Rep.of (Representation.ofDistribMulAction k G P) ⟶
    Rep.of (Representation.ofDistribMulAction k G Q))
  (h : φ ≫ ψ = 0)
  (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
  (hex : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y)

/-- Cupping the lifted differential gives the lifted differential of the cup. -/
theorem connectingCup_lift_d (b : (continuousCochains k G P).X 1)
    (a : (continuousCochains k G M).X 2)
    (ha : ((continuousCoefficientMap φ).f 2).hom a =
      ((continuousCochains k G P).d 1 2).hom b) (d : ContinuousScalarCharacter G k) :
    ((continuousCoefficientMap φ).f 3).hom (integralCupTwo a d) =
      ((continuousCochains k G P).d 2 3).hom (integralCupOne b d) := by
  rw [integralCupTwo_coefficient, ha, integralCupOne_d]

include hφ in
/-- The cup of a connecting representative is a degree-three cocycle. -/
theorem connectingCup_cycle (b : (continuousCochains k G P).X 1)
    (a : (continuousCochains k G M).X 2)
    (ha : ((continuousCoefficientMap φ).f 2).hom a =
      ((continuousCochains k G P).d 1 2).hom b) (d : ContinuousScalarCharacter G k) :
    ((continuousCochains k G M).d 3 4).hom (integralCupTwo a d) = 0 :=
  continuousConnectingMap_cycle φ hφ 2 (integralCupOne b d) (integralCupTwo a d)
    (connectingCup_lift_d φ b a ha d)

/-- The actual connecting map of a cup is the cup of its positive connecting representative. -/
theorem continuousConnectingMap_cup (c : (continuousCochains k G Q).X 1)
    (hc : ((continuousCochains k G Q).d 1 2).hom c = 0)
    (b : (continuousCochains k G P).X 1)
    (hb : ((continuousCoefficientMap ψ).f 1).hom b = c)
    (a : (continuousCochains k G M).X 2)
    (ha : ((continuousCoefficientMap φ).f 2).hom a =
      ((continuousCochains k G P).d 1 2).hom b) (d : ContinuousScalarCharacter G k) :
    (continuousConnectingMap φ ψ h hφ hψ hex 2).hom
        (cochainHomologyClass (continuousCochains k G Q) 2 (integralCupOne c d) (by
          rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 2 3 from rfl)]
          exact integralCupOne_cycle c hc d)) =
      cochainHomologyClass (continuousCochains k G M) 3 (integralCupTwo a d) (by
        rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 3 4 from rfl)]
        exact connectingCup_cycle φ hφ b a ha d) := by
  exact continuousConnectingMap_apply φ ψ h hφ hψ hex 2 (integralCupOne c d)
    (integralCupOne_cycle c hc d) (integralCupOne b d)
    (by rw [integralCupOne_coefficient, hb]) (integralCupTwo a d)
    (connectingCup_lift_d φ b a ha d)

end LocalClassFieldTheory
