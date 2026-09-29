/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyDegreeZero
public import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Cohomology of the actual twisting-sheaf standard-cover complex

The canonical R-linear sheaf comparison gives finite cohomology in every degree,
vanishing outside zero and the top, and the homogeneous polynomial description
in degree zero for at least two charts. Empty and singleton covers are separate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

variable (R : Type u) [CommRing R]

/-- Removing zero summands does not change the direct sum. -/
def zeroSummandsEquiv {κ : Type u} (M : κ → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (p : κ → Prop)
    (h : ∀ i, ¬ p i → Subsingleton (M i)) :
    (⨁ i, M i) ≃ₗ[R] ⨁ i : Subtype p, M i.val := by
  classical
  let f := DFinsupp.subtypeDomainLinearMap R M p
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply DFinsupp.ext
    intro i
    by_cases hi : p i
    · exact congrArg (fun z ↦ z ⟨i, hi⟩) hxy
    · exact (h i hi).elim _ _
  · intro y
    induction y using DFinsupp.induction with
    | h0 => exact ⟨0, map_zero f⟩
    | ha i b y _ _ ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨DFinsupp.single i.val b + x, ?_⟩
      rw [map_add, hx]
      congr 1
      apply DFinsupp.ext
      intro j
      change DFinsupp.single i.val b j.val =
        DFinsupp.single (β := fun i : Subtype p ↦ M i.val) i b j
      by_cases hij : i = j
      · subst j
        simp
      · rw [DFinsupp.single_eq_of_ne (fun he ↦ hij (Subtype.ext he.symm)),
          DFinsupp.single_eq_of_ne (Ne.symm hij)]

open TwistGradedCech

variable (ι : Type u) (n : ℤ)

/-- Empty standard covers have zero cohomology in every degree and every twist. -/
lemma sheaf_isZero_homology_empty [IsEmpty ι] (q : ℕ) :
    IsZero ((sheafComplex R ι n).homology q) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y ↦ (termLinearEquiv R ι n q).injective
    (funext fun a ↦ isEmptyElim (a 0))⟩

/-- Exponents contributing to positive cohomology must be negative everywhere. -/
lemma exponent_isZero_succ_of_not_negative (e : DegreeExponent ι n)
    (h : ¬ ∀ i, e.val i < 0) (q : ℕ) :
    IsZero ((exponentComplex R ι n e.val).homology (q + 1)) := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact exponent_isZero_homology_succ R ι n e.val i hi q

/-- Positive cohomology is the finite direct sum over all-negative exponents. -/
def sheafPositiveHomologyIso [Fintype ι] (q : ℕ) :
    (sheafComplex R ι n).homology (q + 1) ≅
      ModuleCat.of R (⨁ e : NegativeExponent ι n,
        (exponentComplex R ι n e.val.val).homology (q + 1)) :=
  sheafSumHomologyIso R ι n (q + 1) ≪≫
    (zeroSummandsEquiv R _ (fun e : DegreeExponent ι n ↦ ∀ i, e.val i < 0)
      (fun e he ↦ ModuleCat.isZero_iff_subsingleton.mp
        (exponent_isZero_succ_of_not_negative R ι n e he q))).toModuleIso

/-- For at least two charts, a zero-degree contributor must be nonnegative everywhere. -/
lemma exponent_isZero_zero_of_not_nonnegative [Fintype ι]
    (hc : 2 ≤ Fintype.card ι) (e : DegreeExponent ι n)
    (h : ¬ ∀ i, 0 ≤ e.val i) : IsZero ((exponentComplex R ι n e.val).homology 0) := by
  by_cases hn : ∀ i, e.val i < 0
  · exact exponent_isZero_homology_of_negative R ι n e.val 0 (by omega) hn
  · push Not at hn h
    obtain ⟨i, hi⟩ := hn
    obtain ⟨j, hj⟩ := h
    exact exponent_isZero_homology_mixed R ι n e.val i hi j hj 0

/-- Degree-zero cohomology is the finite free module of nonnegative monomials. -/
def sheafZeroCoordinatesIso [Fintype ι] (hc : 2 ≤ Fintype.card ι) :
    (sheafComplex R ι n).homology 0 ≅ ModuleCat.of R (PolynomialCoordinates R ι n) := by
  classical
  have chartsNonempty : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  exact sheafSumHomologyIso R ι n 0 ≪≫
    (zeroSummandsEquiv R _ (fun e : DegreeExponent ι n ↦ ∀ i, 0 ≤ e.val i)
      (fun e he ↦ ModuleCat.isZero_iff_subsingleton.mp
        (exponent_isZero_zero_of_not_nonnegative R ι n hc e he))).toModuleIso ≪≫
    (DFinsupp.mapRange.linearEquiv (fun e : NonnegativeExponent ι n ↦
      (nonnegativeExponentHomologyIso R ι n e.val.val e.val.property
        e.property).toLinearEquiv)).toModuleIso ≪≫
    (finsuppLequivDFinsupp R).symm.toModuleIso

/-- The homogeneous polynomial comparison uses the actual sheaf and canonical base scalars. -/
def sheafZeroPolynomialIso [Fintype ι] (hc : 2 ≤ Fintype.card ι) :
    (sheafComplex R ι n).homology 0 ≅ ModuleCat.of R (integerHomogeneousSubmodule R ι n) :=
  sheafZeroCoordinatesIso R ι n hc ≪≫ (polynomialCoordinatesEquiv R ι n).toModuleIso

/-- In a nonnegative degree, this is the usual homogeneous polynomial submodule. -/
def sheafZeroHomogeneousIso [Fintype ι] (hc : 2 ≤ Fintype.card ι) (m : ℕ) :
    (sheafComplex R ι (m : ℤ)).homology 0 ≅
      ModuleCat.of R (MvPolynomial.homogeneousSubmodule ι R m) :=
  sheafZeroPolynomialIso R ι m hc ≪≫
    (LinearEquiv.ofEq _ _ (integerHomogeneousSubmodule_nat R ι m)).toModuleIso

/-- Negative twists have no degree-zero sections when there are at least two charts. -/
lemma sheaf_isZero_homology_zero_negative [Fintype ι] (hc : 2 ≤ Fintype.card ι)
    (hn : n < 0) : IsZero ((sheafComplex R ι n).homology 0) := by
  have noExponents : IsEmpty (NonnegativeExponent ι n) := nonnegativeExponent_isEmpty ι n hn
  exact (ModuleCat.isZero_iff_subsingleton.mpr (inferInstance :
    Subsingleton (PolynomialCoordinates R ι n))).of_iso (sheafZeroCoordinatesIso R ι n hc)

/-- All positive degrees other than the top vanish, including degrees above the top. -/
lemma sheaf_isZero_homology_off_top [Fintype ι] [Nonempty ι] (q : ℕ)
    (hq : q + 1 ≠ Fintype.card ι - 1) :
    IsZero ((sheafComplex R ι n).homology (q + 1)) := by
  apply sheaf_isZero_homology_of_exponents R ι n (q + 1)
  intro e
  by_cases hn : ∀ i, e.val i < 0
  · exact negativeExponent_isZero_homology R ι n e.val e.property hn (q + 1) hq
  · exact exponent_isZero_succ_of_not_negative R ι n e hn q

/-- Every all-negative exponent homology is a finite R-module in every degree. -/
lemma finiteNegativeExponentHomology [Finite ι] [Nonempty ι]
    (e : NegativeExponent ι n) (q : ℕ) :
    Module.Finite R ((exponentComplex R ι n e.val.val).homology q) := by
  let charts : Fintype ι := Fintype.ofFinite ι
  by_cases hq : q = Fintype.card ι - 1
  · subst q
    exact Module.Finite.equiv (negativeExponentHomologyIso R ι n e.val.val
      e.val.property e.property).symm.toLinearEquiv
  · have zeroHomology : Subsingleton ((exponentComplex R ι n e.val.val).homology q) :=
      ModuleCat.isZero_iff_subsingleton.mp (negativeExponent_isZero_homology R ι n
        e.val.val e.val.property e.property q hq)
    infer_instance

/-- Positive cohomology is finite without a Noetherian or field hypothesis on R. -/
lemma finiteSheafPositiveHomology [Finite ι] [Nonempty ι] (q : ℕ) :
    Module.Finite R ((sheafComplex R ι n).homology (q + 1)) := by
  let charts : Fintype ι := Fintype.ofFinite ι
  have finiteSummands (e : NegativeExponent ι n) :
      Module.Finite R ((exponentComplex R ι n e.val.val).homology (q + 1)) :=
    finiteNegativeExponentHomology R ι n e (q + 1)
  exact Module.Finite.equiv (sheafPositiveHomologyIso R ι n q).symm.toLinearEquiv

/-- On one chart, there is exactly one integer exponent in every total degree. -/
instance uniqueSingletonDegreeExponent [Unique ι] : Unique (DegreeExponent ι n) where
  default := ⟨Finsupp.single default n, by simp⟩
  uniq e := by
    apply Subtype.ext
    have hd : e.val default = n := by
      have hd := congrArg Finsupp.degree (Finsupp.unique_single e.val)
      rw [Finsupp.degree_single] at hd
      exact hd.symm.trans e.property
    exact (Finsupp.unique_single e.val).trans (congrArg (Finsupp.single default) hd)

/-- The single exponent on one chart contributes R even in negative twists. -/
def singletonExponentZeroIso [Fintype ι] [Unique ι] (e : DegreeExponent ι n) :
    (exponentComplex R ι n e.val).homology 0 ≅ ModuleCat.of R R := by
  by_cases hn : 0 ≤ e.val default
  · exact nonnegativeExponentHomologyIso R ι n e.val e.property
      (fun i ↦ by simpa only [Unique.eq_default i] using hn)
  · have hneg : ∀ i, e.val i < 0 := fun i ↦ by
      simpa only [Unique.eq_default i] using lt_of_not_ge hn
    simpa only [Fintype.card_unique, Nat.sub_self] using
      negativeExponentHomologyIso R ι n e.val e.property hneg

/-- Projective zero-space has H0 = R for every integer twist. -/
def sheafSingletonZeroIso [Fintype ι] [Unique ι] :
    (sheafComplex R ι n).homology 0 ≅ ModuleCat.of R R :=
  sheafSumHomologyIso R ι n 0 ≪≫
    (DFinsupp.mapRange.linearEquiv (fun e : DegreeExponent ι n ↦
      (singletonExponentZeroIso R ι n e).toLinearEquiv)).toModuleIso ≪≫
    (DirectSum.lid R R (DegreeExponent ι n)).toModuleIso

/-- All positive cohomology vanishes on projective zero-space for every twist. -/
lemma sheaf_isZero_homology_singleton_succ [Unique ι] (q : ℕ) :
    IsZero ((sheafComplex R ι n).homology (q + 1)) :=
  sheaf_isZero_homology_off_top R ι n q (by simp)

/-- Actual standard-cover twisting-sheaf cohomology is finite in every degree. -/
theorem finiteSheafHomology [Finite ι] (q : ℕ) :
    Module.Finite R ((sheafComplex R ι n).homology q) := by
  let charts : Fintype ι := Fintype.ofFinite ι
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have zeroHomology := ModuleCat.isZero_iff_subsingleton.mp
      (sheaf_isZero_homology_empty R ι n q)
    infer_instance
  | inr h =>
    cases q with
    | succ q => exact finiteSheafPositiveHomology R ι n q
    | zero =>
      by_cases hc : 2 ≤ Fintype.card ι
      · exact Module.Finite.equiv (sheafZeroCoordinatesIso R ι n hc).symm.toLinearEquiv
      · have oneChart : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        let uniqueChart : Unique ι := ⟨⟨Classical.choice h⟩, fun _ ↦ Subsingleton.elim _ _⟩
        exact Module.Finite.equiv (sheafSingletonZeroIso R ι n).symm.toLinearEquiv

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
