/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousExactCoefficients
public import FLT.LocalClassFieldTheory.CochainHomologyClass

/-!
# Connecting maps for continuous coefficients

The boundary comes from the proved short exact sequence of complexes. Its
value is computed by lifting a cocycle and taking its differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k G M P Q : Type u} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k G M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)
local notation "RQ" => Rep.of (Representation.ofDistribMulAction k G Q)

variable (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
    Rep.of (Representation.ofDistribMulAction k G P))
  (ψ : Rep.of (Representation.ofDistribMulAction k G P) ⟶
    Rep.of (Representation.ofDistribMulAction k G Q))
  (h : φ ≫ ψ = 0)
  (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
  (hex : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y)

/-- The canonical boundary of the proved short exact sequence of continuous complexes. -/
def continuousConnectingMap (n : ℕ) :
    (continuousCochains k G Q).homology n ⟶ (continuousCochains k G M).homology (n + 1) :=
  (continuousCoefficientShortComplex_shortExact φ ψ h hφ hψ hex).δ n (n + 1) rfl

include hψ hex in
/-- The differential of a lift comes from a continuous cochain in the kernel coefficients. -/
theorem continuousConnectingMap_lift (n : ℕ) (c : (continuousCochains k G Q).X n)
    (hc : ((continuousCochains k G Q).d n (n + 1)).hom c = 0) :
    ∃ (b : (continuousCochains k G P).X n) (a : (continuousCochains k G M).X (n + 1)),
      ((continuousCoefficientMap ψ).f n).hom b = c ∧
      ((continuousCoefficientMap φ).f (n + 1)).hom a =
        ((continuousCochains k G P).d n (n + 1)).hom b := by
  obtain ⟨b, hb⟩ := continuousCoefficientMap_surjective ψ hψ n c
  have hz : ((continuousCoefficientMap ψ).f (n + 1)).hom
      (((continuousCochains k G P).d n (n + 1)).hom b) = 0 := by
    have he := congrArg (fun f => f.hom b) ((continuousCoefficientMap ψ).comm n (n + 1))
    change ((continuousCochains k G Q).d n (n + 1)).hom
      (((continuousCoefficientMap ψ).f n).hom b) = _ at he
    rw [hb, hc] at he
    exact he.symm
  obtain ⟨a, ha⟩ := continuousCoefficientMap_exact φ ψ hex (n + 1) _ hz
  exact ⟨b, a, hb, ha⟩

include hφ in
/-- The preimage of a lifted differential is a cocycle. -/
theorem continuousConnectingMap_cycle (n : ℕ) (b : (continuousCochains k G P).X n)
    (a : (continuousCochains k G M).X (n + 1))
    (ha : ((continuousCoefficientMap φ).f (n + 1)).hom a =
      ((continuousCochains k G P).d n (n + 1)).hom b) :
    ((continuousCochains k G M).d (n + 1) (n + 2)).hom a = 0 := by
  apply continuousCoefficientMap_injective φ hφ (n + 2)
  have he := congrArg (fun f => f.hom a)
    ((continuousCoefficientMap φ).comm (n + 1) (n + 2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he
  rw [map_zero, ← he]
  change ((continuousCochains k G P).d (n + 1) (n + 2)).hom
    (((continuousCoefficientMap φ).f (n + 1)).hom a) = 0
  rw [ha]
  exact congrArg (fun f => f.hom b) ((continuousCochains k G P).d_comp_d n (n + 1) (n + 2))

/-- The categorical boundary has the positive lifted-differential formula. -/
theorem continuousConnectingMap_apply (n : ℕ) (c : (continuousCochains k G Q).X n)
    (hc : ((continuousCochains k G Q).d n (n + 1)).hom c = 0)
    (b : (continuousCochains k G P).X n) (hb : ((continuousCoefficientMap ψ).f n).hom b = c)
    (a : (continuousCochains k G M).X (n + 1))
    (ha : ((continuousCoefficientMap φ).f (n + 1)).hom a =
      ((continuousCochains k G P).d n (n + 1)).hom b) :
    (continuousConnectingMap φ ψ h hφ hψ hex n).hom
        (cochainHomologyClass (continuousCochains k G Q) n c (by
          rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
          exact hc)) =
      cochainHomologyClass (continuousCochains k G M) (n + 1) a
        (by
          rw [(ComplexShape.up ℕ).next_eq'
            (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl)]
          exact continuousConnectingMap_cycle φ hφ n b a ha) := by
  exact (continuousCoefficientShortComplex_shortExact φ ψ h hφ hψ hex).δ_apply
    n (n + 1) rfl c hc b hb a ha (n + 2)
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))

end LocalClassFieldTheory
