/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAbstractGoodReductionClosure
public import FLT.Mazur.EllipticMultiplicativeValuationEquation
public import FLT.Mazur.EllipticSmallRamificationComponents
public import FLT.Mazur.ValuationRingCompleteModel

/-!
# Small-ramification component injection for the original prime subgroup

The complete extension DVR and original variable change retain their identities.
Small absolute ramification eliminates the formal-kernel branch: every original
nonzero p-torsion generator injects into the split nodal component quotient.
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

/-- The actual split-component injection for every original nonzero prime-torsion point. -/
def AbstractPrimeComponentInjection : Prop :=
  ∀ (P : (W.map (algebraMap R K)).toAffine.Point), p • P = 0 → P ≠ 0 →
    let H := abstractExtensionProjectiveSubgroup W U C hC P
    ((V).nodePoly.map (residue A)).Splits ∧
        Function.Injective (ellipticSubgroupComponentHom A V H) ∧
        ∃ n : ℕ, 0 < n ∧ (V).Δ ∈ maximalIdeal A ^ n ∧
          (V).Δ ∉ maximalIdeal A ^ (n + 1) ∧ p ∣ n

variable [CharZero L] [IsAdicComplete (maximalIdeal S) S]
  [Finite (ResidueField S)] [Fact p.Prime] [CharP (ResidueField S) p]

/-- The actual multiplicative S2a equation gives injective components for every generator. -/
theorem abstractPrimeComponentInjection_of_multiplicative
    [(U.map (algebraMap S L)).HasMultiplicativeReduction S] (hp2 : 2 < p)
    (he : RaynaudParameters.order (p : S) < p - 1) :
    AbstractPrimeComponentInjection (K := K) W U C hC p := by
  let _ : IsAdicComplete (maximalIdeal A) A := fractionValuationSubring_isAdicComplete S L
  let _ : Finite (ResidueField A) := fractionValuationSubring_residue_finite S L
  let _ : CharP (ResidueField A) p := fractionValuationSubring_residue_char S L p
  let _ : ((V).map (algebraMap A L)).IsElliptic :=
    fractionValuationEquation_generic_isElliptic U _ C hC
  intro P hP hP0
  let H := abstractExtensionProjectiveSubgroup W U C hC P
  have hc : Nat.card H = p := abstractExtensionProjectiveSubgroup_card W U C hC P p hP hP0
  obtain ⟨hd, hu⟩ := fractionValuationEquation_multiplicative_invariants (L := L) U
  apply primeSubgroup_split_components_small_ramification A V p
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) _ H hc hd hu hp2
  rwa [fractionValuationSubring_prime_order]

end FLT.Mazur
