/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousConnectingMap
public import FLT.LocalClassFieldTheory.ContinuousRestriction
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Connecting maps commute with continuous group restriction

Pulling back the group arguments and mapping coefficients gives an actual
morphism of short complexes. Its connecting square commutes in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k G H M P Q M' P' Q' : Type u} [CommRing k] [Group G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [Module k M] [DistribMulAction H M] [SMulCommClass H k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul H M]
  [AddCommGroup P] [Module k P] [DistribMulAction H P] [SMulCommClass H k P]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul H P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction H Q] [SMulCommClass H k Q]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul H Q]
  [AddCommGroup M'] [Module k M'] [DistribMulAction G M'] [SMulCommClass G k M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul G M']
  [AddCommGroup P'] [Module k P'] [DistribMulAction G P'] [SMulCommClass G k P']
  [TopologicalSpace P'] [DiscreteTopology P'] [ContinuousSMul G P']
  [AddCommGroup Q'] [Module k Q'] [DistribMulAction G Q'] [SMulCommClass G k Q']
  [TopologicalSpace Q'] [DiscreteTopology Q'] [ContinuousSMul G Q']

variable (φ : (Rep.of (Representation.ofDistribMulAction k H M)) ⟶ (Rep.of
    (Representation.ofDistribMulAction k H P))) (ψ : (Rep.of (Representation.ofDistribMulAction k
    H P)) ⟶ (Rep.of (Representation.ofDistribMulAction k H Q))) (h : φ ≫ ψ = 0)
  (φ' : (Rep.of (Representation.ofDistribMulAction k G M')) ⟶ (Rep.of
    (Representation.ofDistribMulAction k G P'))) (ψ' : (Rep.of (Representation.ofDistribMulAction
    k G P')) ⟶ (Rep.of (Representation.ofDistribMulAction k G Q'))) (h' : φ' ≫ ψ' = 0)
  (f : G →* H) (hf : Continuous f)
  (α : Rep.res f (Rep.of (Representation.ofDistribMulAction k H M)) ⟶ (Rep.of
    (Representation.ofDistribMulAction k G M'))) (β : Rep.res f (Rep.of
    (Representation.ofDistribMulAction k H P)) ⟶ (Rep.of (Representation.ofDistribMulAction k G
    P'))) (γ : Rep.res f (Rep.of (Representation.ofDistribMulAction k H Q)) ⟶ (Rep.of
    (Representation.ofDistribMulAction k G Q')))
  (hα : ∀ x : M, β.hom (φ.hom x) = φ'.hom (α.hom x))
  (hβ : ∀ x : P, γ.hom (ψ.hom x) = ψ'.hom (β.hom x))

/-- Restriction with commuting coefficient maps induces a morphism of short complexes. -/
def continuousRestrictionSequenceMap :
    continuousCoefficientShortComplex φ ψ h ⟶ continuousCoefficientShortComplex φ' ψ' h' where
  τ₁ := continuousRestriction f hf α
  τ₂ := continuousRestriction f hf β
  τ₃ := continuousRestriction f hf γ
  comm₁₂ := by
    ext n c : 3
    apply Subtype.ext
    funext x
    exact (hα (c.val (f ∘ x))).symm
  comm₂₃ := by
    ext n c : 3
    apply Subtype.ext
    funext x
    exact (hβ (c.val (f ∘ x))).symm

include β hα hβ in
/-- The connecting square commutes for any morphism of discrete exact coefficient sequences. -/
theorem continuousConnectingMap_restriction_naturality
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
    (hex : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y)
    (hφ' : Function.Injective φ'.hom) (hψ' : Function.Surjective ψ'.hom)
    (hex' : ∀ y : P', ψ'.hom y = 0 ↔ ∃ x : M', φ'.hom x = y) (n : ℕ) :
    continuousConnectingMap φ ψ h hφ hψ hex n ≫
        homologyMap (continuousRestriction f hf α) (n + 1) =
      homologyMap (continuousRestriction f hf γ) n ≫
        continuousConnectingMap φ' ψ' h' hφ' hψ' hex' n :=
  HomologySequence.δ_naturality
    (continuousRestrictionSequenceMap φ ψ h φ' ψ' h' f hf α β γ hα hβ)
    (continuousCoefficientShortComplex_shortExact φ ψ h hφ hψ hex)
    (continuousCoefficientShortComplex_shortExact φ' ψ' h' hφ' hψ' hex') n (n + 1) rfl

end LocalClassFieldTheory
