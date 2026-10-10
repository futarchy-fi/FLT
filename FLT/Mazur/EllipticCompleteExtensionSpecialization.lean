/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticCompleteSemistableExtension
public import FLT.Mazur.EllipticAbstractGoodReductionClosure

/-!
# Good-branch specialization for the constructed complete semistable extension

Choose exactly the extension, integral closure, equation and variable change
provided by S2a. In its good branch every original nonzero p-torsion point
has an etale closure and injective smooth reduction in the canonical valuation
realization. No second extension or change of variables is introduced.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing EllipticSubgroupChart

section Consequence

variable {R S K L : Type} [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Algebra S L] [IsFractionRing S L] [DecidableEq K] [DecidableEq L]
  (W : WeierstrassCurve R) (U : WeierstrassCurve S)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap S L)) (p : ℕ)

local notation "A" => fractionValuationSubring S L
local notation "V" => fractionValuationEquation (L := L) U

/-- The concrete closure and smooth-reduction conclusions for all original p-torsion points. -/
def AbstractPrimeSpecialization : Prop :=
  ∀ (P : (W.map (algebraMap R K)).toAffine.Point), p • P = 0 → P ≠ 0 →
    let H := abstractExtensionProjectiveSubgroup W U C hC P
    ∃ hΔ : IsUnit (V).Δ, Finite H ∧ Algebra.Etale A (GlobalClosure A V H) ∧
      Function.Injective (subgroupSmoothReduction A V H
        (subgroup_le_ellipticE0_of_unit_discriminant A V H hΔ))

variable [CharZero L] [HenselianLocalRing S] [Fact p.Prime] [CharP (ResidueField S) p]

/-- The specialization conclusion is constructed from good reduction and small ramification. -/
theorem abstractPrimeSpecialization_of_goodReduction
    [(U.map (algebraMap S L)).HasGoodReduction S]
    (he : RaynaudParameters.order (p : S) < p - 1) :
    AbstractPrimeSpecialization (K := K) W U C hC p := by
  intro P hP hP0
  exact ⟨fractionValuationEquation_discriminant_unit U,
    abstractExtensionProjectiveSubgroup_finite W U C hC P p hP hP0,
    abstractExtensionGoodReductionClosure_etale W U C hC P p hP hP0 he,
    abstractExtensionGoodReduction_specialization_injective W U C hC P p hP hP0 he⟩

end Consequence

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]

/-- The actual S2a witnesses also provide good-branch specialization for the original points. -/
theorem exists_complete_semistable_extension_specialization (p : ℕ) [Fact p.Prime]
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
        AbstractPrimeSpecialization (K := K) W U C hC p) := by
  classical
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, U, C, complete, hensel, char, finite, hdeg, he, he', hred, hC⟩ :=
    exists_complete_semistable_extension (K := K) p hp hp17 W hΔ
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hell : (W.map (algebraMap R L)).IsElliptic := by
    rw [isElliptic_iff, map_Δ, isUnit_iff_ne_zero]
    exact fun h => hΔ (hinj (h.trans (map_zero _).symm))
  let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  refine ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, inferInstance, hell, U, C, hC, complete, hensel, char, finite,
    hdeg, he, he', hred, ?_⟩
  intro hgood
  exact abstractPrimeSpecialization_of_goodReduction (K := K) W U C hC p he'

end FLT.Mazur
