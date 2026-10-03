/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousConnectingMap
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Connecting maps are natural in the coefficient sequence

Commuting coefficient squares induce a morphism of the constructed short
complexes. The homology sequence then gives the connecting square.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k G M P Q M' P' Q' : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]
  [AddCommGroup M'] [Module k M'] [DistribMulAction G M'] [SMulCommClass G k M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul G M']
  [AddCommGroup P'] [Module k P'] [DistribMulAction G P'] [SMulCommClass G k P']
  [TopologicalSpace P'] [DiscreteTopology P'] [ContinuousSMul G P']
  [AddCommGroup Q'] [Module k Q'] [DistribMulAction G Q'] [SMulCommClass G k Q']
  [TopologicalSpace Q'] [DiscreteTopology Q'] [ContinuousSMul G Q']

variable (φ : (Rep.of (Representation.ofDistribMulAction k G M)) ⟶ (Rep.of
    (Representation.ofDistribMulAction k G P))) (ψ : (Rep.of (Representation.ofDistribMulAction k
    G P)) ⟶ (Rep.of (Representation.ofDistribMulAction k G Q))) (h : φ ≫ ψ = 0)
  (φ' : (Rep.of (Representation.ofDistribMulAction k G M')) ⟶ (Rep.of
    (Representation.ofDistribMulAction k G P'))) (ψ' : (Rep.of (Representation.ofDistribMulAction
    k G P')) ⟶ (Rep.of (Representation.ofDistribMulAction k G Q'))) (h' : φ' ≫ ψ' = 0)
  (α : (Rep.of (Representation.ofDistribMulAction k G M)) ⟶ (Rep.of
    (Representation.ofDistribMulAction k G M'))) (β : (Rep.of (Representation.ofDistribMulAction k
    G P)) ⟶ (Rep.of (Representation.ofDistribMulAction k G P'))) (γ : (Rep.of
    (Representation.ofDistribMulAction k G Q)) ⟶ (Rep.of (Representation.ofDistribMulAction k G
    Q')))
  (hα : φ ≫ β = α ≫ φ') (hβ : ψ ≫ γ = β ≫ ψ')

/-- Commuting coefficient squares give a morphism of actual continuous short complexes. -/
def continuousCoefficientSequenceMap :
    continuousCoefficientShortComplex φ ψ h ⟶ continuousCoefficientShortComplex φ' ψ' h' where
  τ₁ := continuousCoefficientMap α
  τ₂ := continuousCoefficientMap β
  τ₃ := continuousCoefficientMap γ
  comm₁₂ := by
    change continuousCoefficientMap α ≫ continuousCoefficientMap φ' =
      continuousCoefficientMap φ ≫ continuousCoefficientMap β
    rw [← continuousCoefficientMap_comp, ← continuousCoefficientMap_comp, hα]
  comm₂₃ := by
    change continuousCoefficientMap β ≫ continuousCoefficientMap ψ' =
      continuousCoefficientMap ψ ≫ continuousCoefficientMap γ
    rw [← continuousCoefficientMap_comp, ← continuousCoefficientMap_comp, hβ]

include β hα hβ in
/-- The connecting square commutes for any morphism of discrete exact coefficient sequences. -/
theorem continuousConnectingMap_coefficient_naturality
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
    (hex : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y)
    (hφ' : Function.Injective φ'.hom) (hψ' : Function.Surjective ψ'.hom)
    (hex' : ∀ y : P', ψ'.hom y = 0 ↔ ∃ x : M', φ'.hom x = y) (n : ℕ) :
    continuousConnectingMap φ ψ h hφ hψ hex n ≫
        homologyMap (continuousCoefficientMap α) (n + 1) =
      homologyMap (continuousCoefficientMap γ) n ≫
        continuousConnectingMap φ' ψ' h' hφ' hψ' hex' n :=
  HomologySequence.δ_naturality
    (continuousCoefficientSequenceMap φ ψ h φ' ψ' h' α β γ hα hβ)
    (continuousCoefficientShortComplex_shortExact φ ψ h hφ hψ hex)
    (continuousCoefficientShortComplex_shortExact φ' ψ' h' hφ' hψ' hex') n (n + 1) rfl

end LocalClassFieldTheory
