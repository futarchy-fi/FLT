/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAbstractGoodReductionClosure
public import FLT.Mazur.EllipticMultiplicativeValuationEquation
public import FLT.Mazur.EllipticPrimeSubgroupComponents

/-!
# The original prime subgroup in the multiplicative branch

The same abstract extension DVR and variable change give a precise alternative:
all subgroup points have smooth reduction, or the node is split and the subgroup
injects into the actual component quotient, forcing p-divisible discriminant depth.
This comparison does not assert a Hopf structure on the nodal closure.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R S K L : Type} [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Algebra S L] [IsFractionRing S L] [DecidableEq K] [DecidableEq L]
  (W : WeierstrassCurve R) (U : WeierstrassCurve S)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap S L)) (p : ℕ)

local notation "A" => fractionValuationSubring S L
local notation "V" => fractionValuationEquation (L := L) U

local instance : IsDiscreteValuationRing A := fractionValuationSubring_isDiscreteValuationRing S L

/-- The concrete smooth-containment or split-component conclusion for the original points. -/
def AbstractPrimeComponentAlternative : Prop :=
  ∀ (P : (W.map (algebraMap R K)).toAffine.Point), p • P = 0 → P ≠ 0 →
    let H := abstractExtensionProjectiveSubgroup W U C hC P
    H ≤ ellipticE0 A V ∨
      ((V).nodePoly.map (residue A)).Splits ∧
        Function.Injective (ellipticSubgroupComponentHom A V H) ∧
        ∃ n : ℕ, 0 < n ∧ (V).Δ ∈ maximalIdeal A ^ n ∧
          (V).Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n

variable [Finite (ResidueField S)] [Fact p.Prime]

/-- The actual multiplicative S2a equation gives the component alternative for every generator. -/
theorem abstractPrimeComponentAlternative_of_multiplicative
    [(U.map (algebraMap S L)).HasMultiplicativeReduction S] (hp2 : 2 < p) :
    AbstractPrimeComponentAlternative (K := K) W U C hC p := by
  let _ : Finite (ResidueField A) := fractionValuationSubring_residue_finite S L
  let _ : ((V).map (algebraMap A L)).IsElliptic :=
    fractionValuationEquation_generic_isElliptic U _ C hC
  intro P hP hP0
  let H := abstractExtensionProjectiveSubgroup W U C hC P
  have hc : Nat.card H = p := abstractExtensionProjectiveSubgroup_card W U C hC P p hP hP0
  obtain ⟨hd, hu⟩ := fractionValuationEquation_multiplicative_invariants (L := L) U
  by_cases hH : H ≤ ellipticE0 A V
  · exact Or.inl hH
  · right
    have hs : ((V).nodePoly.map (residue A)).Splits := by
      by_contra hns
      exact hH (primeSubgroup_le_ellipticE0_nonsplitNodal A V H p hc hd hu hns hp2)
    exact ⟨hs, (primeSubgroup_smooth_or_component_injective A V H p hc).resolve_left hH,
      primeSubgroup_splitNode_depth_dvd A V H p hc hd hu hs hH⟩

end FLT.Mazur
