/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCompleteExtensionSpecialization
public import FLT.Mazur.EllipticAbstractComponentInjection

/-!
# Injective specialization or components for the exact S2a witnesses

The constructed complete semistable extension simultaneously retains the
proved good-branch closure specialization and injectivity in the bad-branch
component quotient, for every original nonzero p-torsion point.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]

/-- Both reduction branches have their concrete comparison for the same S2a witnesses. -/
theorem exists_complete_semistable_extension_injections (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField R) p] (hp : Irreducible (p : R)) (hp17 : 17 ≤ p)
    (W : WeierstrassCurve R) (hΔ : W.Δ ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L)
      (_ : IsFractionRing S L) (_ : IsIntegralClosure S R L)
      (_ : DecidableEq L) (_ : (W.map (algebraMap R L)).IsElliptic)
      (U : WeierstrassCurve S) (C : VariableChange L)
      (hC : C • W.map (algebraMap R L) = U.map (algebraMap S L)),
      IsAdicComplete (maximalIdeal S) S ∧ HenselianLocalRing S ∧
      CharP (ResidueField S) p ∧ Finite (ResidueField S) ∧
      Module.finrank K L ≤ 6 ∧ (maximalIdeal S).ramificationIdx R ≤ 6 ∧
      RaynaudParameters.order (p : S) < p - 1 ∧
      ((U.map (algebraMap S L)).HasGoodReduction S ∨
        (U.map (algebraMap S L)).HasMultiplicativeReduction S) ∧
      ((U.map (algebraMap S L)).HasGoodReduction S →
        AbstractPrimeSpecialization (K := K) W U C hC p) ∧
      ((U.map (algebraMap S L)).HasMultiplicativeReduction S →
        AbstractPrimeComponentInjection (K := K) W U C hC p) := by
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, dec, hell, U, C, hC, complete, hensel, char, finite,
    hdeg, he, he', hred, hgood⟩ :=
    exists_complete_semistable_extension_specialization (K := K) p hp hp17 W hΔ
  refine ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, dec, hell, U, C, hC, complete, hensel, char, finite,
    hdeg, he, he', hred, hgood, ?_⟩
  let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro hmult
  exact abstractPrimeComponentInjection_of_multiplicative (K := K) W U C hC p (by omega) he'

end FLT.Mazur
