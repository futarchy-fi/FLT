/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyFullSupport
public import FLT.Mazur.ProjectiveTwistCechCohomologySumHomology
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Data.Int.Interval

/-!
# Degree-zero cohomology and finite exponent sets

Constant cocycles compute the nonnegative exponent summands. Integer exponent
bounds give finite free polynomial coordinates, including the zero negative pieces.
The empty cover and the one-chart exception are handled at the sheaf endpoint.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

open LocalizationDegree TwistGradedCech

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Evaluation identifies constant zero-cocycles with the coefficient ring. -/
def emptySupportCyclesEquiv (j : ι) :
    LinearMap.ker ((supportComplex R ι ∅).sc 0).g.hom ≃ₗ[R] R where
  toFun x := x.val.val (fun _ ↦ j)
  invFun r := ⟨⟨fun _ ↦ r, fun _ h ↦ False.elim (h (Set.empty_subset _))⟩, by
    simp only [LinearMap.mem_ker]
    change (supportComplex R ι ∅).d 0 ((ComplexShape.up ℕ).next 0) _ = 0
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl)]
    change supportDifferential R ι ∅ 0 _ = 0
    apply Subtype.ext
    funext a
    change (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • r) = 0
    simp [Fin.sum_univ_two]⟩
  left_inv x := by
    have hx : supportDifferential R ι ∅ 0 x.val = 0 := by
      have hx := x.property
      change (supportComplex R ι ∅).d 0 ((ComplexShape.up ℕ).next 0) x.val = 0 at hx
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl)] at hx
      exact hx
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact (support_zero_cocycle_constant R ι ∅ j x.val hx a).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- There are no incoming boundaries in degree zero. -/
def emptySupportHomologyIso (j : ι) :
    (supportComplex R ι ∅).homology 0 ≅ ModuleCat.of R R :=
  (((supportComplex R ι ∅).sc 0).asIsoHomologyπ (by
    simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', supportComplex, CochainComplex.of.d])).symm ≪≫
    ((supportComplex R ι ∅).sc 0).moduleCatCyclesIso ≪≫
    (emptySupportCyclesEquiv R ι j).toModuleIso

/-- Each nonnegative exponent contributes a copy of R to degree-zero cohomology. -/
def nonnegativeExponentHomologyIso [Nonempty ι] (n : ℤ) (e : ι →₀ ℤ)
    (he : e.degree = n) (hnonneg : ∀ i, 0 ≤ e i) :
    (exponentComplex R ι n e).homology 0 ≅ ModuleCat.of R R :=
  HomologicalComplex.homologyMapIso (exponentSupportIso R ι n e he) 0 ≪≫
    HomologicalComplex.homologyMapIso
      (eqToIso (congrArg (supportComplex R ι) (show {i | e i < 0} = ∅ from by
        ext i
        simp [not_lt_of_ge (hnonneg i)]))) 0 ≪≫
    emptySupportHomologyIso R ι (Classical.choice inferInstance)

/-- Degree-n exponents with no negative coordinate. -/
abbrev NonnegativeExponent (n : ℤ) := {e : DegreeExponent ι n // ∀ i, 0 ≤ e.val i}

/-- Degree-n exponents with every coordinate strictly negative. -/
abbrev NegativeExponent (n : ℤ) := {e : DegreeExponent ι n // ∀ i, e.val i < 0}

variable (n : ℤ)

/-- A nonnegative coordinate is bounded by the total degree. -/
lemma nonnegativeExponent_le [Finite ι] (e : NonnegativeExponent ι n) (i : ι) :
    e.val.val i ≤ n := by
  let charts : Fintype ι := Fintype.ofFinite ι
  have hd := e.val.property
  rw [Finsupp.degree_eq_sum] at hd
  exact (Finset.single_le_sum (fun j _ ↦ e.property j) (Finset.mem_univ i)).trans_eq hd

/-- A negative coordinate is bounded below by the total degree. -/
lemma negativeExponent_ge [Finite ι] (e : NegativeExponent ι n) (i : ι) :
    n ≤ e.val.val i := by
  let charts : Fintype ι := Fintype.ofFinite ι
  have hd := e.val.property
  rw [Finsupp.degree_eq_sum] at hd
  have hs : -e.val.val i ≤ ∑ j, -e.val.val j :=
    Finset.single_le_sum (fun j _ ↦ neg_nonneg.mpr (e.property j).le) (Finset.mem_univ i)
  rw [Finset.sum_neg_distrib, hd] at hs
  omega

/-- Nonnegative exponent sets of fixed degree are finite, also for an empty index set. -/
instance finiteNonnegativeExponent [Finite ι] : Finite (NonnegativeExponent ι n) := by
  let charts : Fintype ι := Fintype.ofFinite ι
  let f : NonnegativeExponent ι n → (ι → Set.Icc (0 : ℤ) n) :=
    fun e i ↦ ⟨e.val.val i, e.property i, nonnegativeExponent_le ι n e i⟩
  exact Finite.of_injective f (fun x y h ↦ Subtype.ext (Subtype.ext
    (Finsupp.ext fun i ↦ congrArg Subtype.val (congrFun h i))))

/-- All-negative exponent sets of fixed degree are finite without assumptions on R. -/
instance finiteNegativeExponent [Finite ι] : Finite (NegativeExponent ι n) := by
  let charts : Fintype ι := Fintype.ofFinite ι
  let f : NegativeExponent ι n → (ι → Set.Icc n (0 : ℤ)) :=
    fun e i ↦ ⟨e.val.val i, negativeExponent_ge ι n e i, (e.property i).le⟩
  exact Finite.of_injective f (fun x y h ↦ Subtype.ext (Subtype.ext
    (Finsupp.ext fun i ↦ congrArg Subtype.val (congrFun h i))))

/-- The finite free module of nonnegative exponent coefficients. -/
abbrev PolynomialCoordinates := NonnegativeExponent ι n →₀ R

instance finitePolynomialCoordinates [Finite ι] :
    Module.Finite R (PolynomialCoordinates R ι n) := inferInstance

instance freePolynomialCoordinates : Module.Free R (PolynomialCoordinates R ι n) :=
  inferInstance

/-- A nonnegative exponent has nonnegative total degree. -/
lemma nonnegativeExponent_degree [Finite ι] (e : NonnegativeExponent ι n) : 0 ≤ n := by
  let charts : Fintype ι := Fintype.ofFinite ι
  have hd := e.val.property
  rw [Finsupp.degree_eq_sum] at hd
  rw [← hd]
  exact Finset.sum_nonneg (fun i _ ↦ e.property i)

/-- In negative polynomial degrees the exponent set is empty, even with no variables. -/
lemma nonnegativeExponent_isEmpty [Finite ι] (hn : n < 0) :
    IsEmpty (NonnegativeExponent ι n) := by
  let charts : Fintype ι := Fintype.ofFinite ι
  exact ⟨fun e ↦ (not_le_of_gt hn) (nonnegativeExponent_degree ι n e)⟩

/-- Casting natural exponents identifies precisely the nonnegative integer exponents. -/
def naturalExponentEquiv : {d : ι →₀ ℕ // (d.degree : ℤ) = n} ≃
    NonnegativeExponent ι n where
  toFun d := ⟨⟨exponentInt d.val, by simpa using d.property⟩, fun i ↦ by simp⟩
  invFun e := ⟨Finsupp.mapRange Int.toNat (by rfl) e.val.val, by
    have h : exponentInt (Finsupp.mapRange Int.toNat (by rfl) e.val.val) = e.val.val := by
      ext i
      exact Int.toNat_of_nonneg (e.property i)
    rw [← exponentInt_degree, h, e.val.property]⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    exact Int.toNat_natCast _
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    exact Int.toNat_of_nonneg (e.property i)

/-- The integer-graded polynomial piece, defined by its actual monomial support. -/
def integerHomogeneousSubmodule : Submodule R (MvPolynomial ι R) :=
  AddMonoidAlgebra.supported R R {d : ι →₀ ℕ | (d.degree : ℤ) = n}

/-- Polynomial coordinates are R-linearly the degree-n homogeneous polynomials. -/
def polynomialCoordinatesEquiv :
    PolynomialCoordinates R ι n ≃ₗ[R] integerHomogeneousSubmodule R ι n :=
  (Finsupp.domLCongr (naturalExponentEquiv ι n).symm).trans
    (AddMonoidAlgebra.supportedEquivFinsupp _).symm

/-- At a natural degree the integer-indexed piece is the usual homogeneous submodule. -/
lemma integerHomogeneousSubmodule_nat (m : ℕ) :
    integerHomogeneousSubmodule R ι (m : ℤ) = MvPolynomial.homogeneousSubmodule ι R m := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  simp only [integerHomogeneousSubmodule, Nat.cast_inj]

/-- Negative homogeneous polynomial pieces are zero. -/
lemma integerHomogeneousSubmodule_negative (hn : n < 0) :
    integerHomogeneousSubmodule R ι n = ⊥ := by
  have h : {d : ι →₀ ℕ | (d.degree : ℤ) = n} = ∅ := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hd ↦ (not_lt_of_ge (Int.natCast_nonneg d.degree)) (hd ▸ hn)
  simp [integerHomogeneousSubmodule, h, AddMonoidAlgebra.supported]

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
