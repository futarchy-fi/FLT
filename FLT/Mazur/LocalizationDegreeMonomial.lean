/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationDegreeFace

/-!
# Monomial fractions in integer degree pieces

Concrete monomial fractions span each degree piece over any commutative ring.
Their integer exponents have the prescribed degree and are nonnegative outside
of the tuple. Clearing a common denominator constructs the presentation; Laurent
coefficients give its inverse. The resulting linear equivalence identifies the
actual restriction maps with inclusions of exponent sets.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.ProjectiveSpace.LocalizationDegree

universe u

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {q : ℕ} (a : Fin (q + 1) → ι)

/-- Division by a fixed coordinate-product power is linear over the base ring. -/
def fractionLinear (k : ℕ) : MvPolynomial ι R →ₗ[R] Full R ι a where
  toFun f := fraction R ι a f k
  map_add' f g := (Localization.add_mk_self f _ g).symm
  map_smul' r f := (fraction_smul R ι a r f k).symm

/-- A homogeneous monomial numerator gives an element of the expected degree. -/
lemma monomialFraction_mem (s : ι →₀ ℕ) (r : R) (k : ℕ) :
    fraction R ι a (monomial s r) k ∈
      piece R ι a ((s.degree : ℤ) - k * (q + 1)) :=
  ⟨k, s.degree, monomial s r, isHomogeneous_monomial r rfl, rfl, rfl⟩

/-- A fraction is the sum of its monomial numerator fractions at one denominator. -/
lemma fraction_eq_sum (f : MvPolynomial ι R) (k : ℕ) :
    fraction R ι a f k =
      ∑ s ∈ f.support, fraction R ι a (monomial s (f.coeff s)) k := by
  classical
  exact congrArg (fractionLinear R ι a k) f.as_sum |>.trans (map_sum _ _ _)

/-- Unit-coefficient monomial fractions generate the actual degree piece. -/
lemma piece_eq_span_monomial (n : ℤ) :
    piece R ι a n = Submodule.span R
      {x | ∃ (s : ι →₀ ℕ) (k : ℕ), (s.degree : ℤ) - k * (q + 1) = n ∧
        fraction R ι a (monomial s 1) k = x} := by
  classical
  apply le_antisymm
  · rintro x ⟨k, d, f, hf, hd, rfl⟩
    rw [fraction_eq_sum]
    apply Submodule.sum_mem
    intro s hs
    have hdeg : s.degree = d :=
      (IsHomogeneous.degree_eq_sum_deg_support hf hs).symm
    have hm : fraction R ι a (monomial s 1) k ∈ Submodule.span R
        {x | ∃ (s : ι →₀ ℕ) (k : ℕ), (s.degree : ℤ) - k * (q + 1) = n ∧
          fraction R ι a (monomial s 1) k = x} :=
      Submodule.subset_span ⟨s, k, by simpa only [hdeg] using hd, rfl⟩
    convert (Submodule.smul_mem _ (f.coeff s) hm) using 1
    rw [fraction_smul, ← (monomial s).map_smul]
    simp only [smul_eq_mul, mul_one]
  · apply Submodule.span_le.mpr
    rintro x ⟨s, k, hn, rfl⟩
    rw [← hn]
    exact monomialFraction_mem R ι a s 1 k

variable {R ι}

/-- The multiplicities of the tuple's coordinates, retaining repeated indices. -/
def coordinateExponent {m : ℕ} (b : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (b j) 1

lemma coordinateExponent_degree {m : ℕ} (b : Fin m → ι) :
    (coordinateExponent b).degree = m := by
  simp [coordinateExponent, map_sum]

lemma coordinateExponent_outside {m : ℕ} (b : Fin m → ι) (i : ι)
    (hi : i ∉ Set.range b) : coordinateExponent b i = 0 := by
  classical
  have h (j : Fin m) : b j ≠ i := fun h ↦ hi ⟨j, h⟩
  simp [coordinateExponent, Finsupp.finsetSum_apply, h]

lemma coordinateExponent_face (q : ℕ) (b : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    coordinateExponent b =
      coordinateExponent (b ∘ k.succAbove) + Finsupp.single (b k) 1 := by
  exact (Fin.sum_univ_succAbove (fun j ↦ Finsupp.single (b j) 1) k).trans (add_comm _ _)

lemma coordinateProduct_eq_monomial {m : ℕ} (b : Fin m → ι) :
    TwistCech.coordinateProduct R ι b = monomial (coordinateExponent b) 1 := by
  classical
  simp only [TwistCech.coordinateProduct, coordinateExponent, monomial_sum_one, X]

/-- Coefficientwise inclusion of natural exponents into integer exponents. -/
def exponentInt : (ι →₀ ℕ) →+ (ι →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

@[simp] lemma exponentInt_apply (s : ι →₀ ℕ) (i : ι) :
    exponentInt s i = (s i : ℤ) := rfl

@[simp] lemma exponentInt_degree (s : ι →₀ ℕ) :
    (exponentInt s).degree = (s.degree : ℤ) := by
  change (Finsupp.mapRange (fun x : ℕ ↦ (x : ℤ)) (by rfl) s).sum
    (fun _ x ↦ x) = _
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp [Finsupp.sum, Finsupp.degree_apply]

/-- The integer exponent represented by a numerator and denominator power. -/
def fractionExponent (s : ι →₀ ℕ) (k : ℕ) : ι →₀ ℤ :=
  exponentInt s - k • exponentInt (coordinateExponent a)

lemma fractionExponent_degree (s : ι →₀ ℕ) (k : ℕ) :
    (fractionExponent a s k).degree = (s.degree : ℤ) - k * (q + 1) := by
  simp [fractionExponent, map_sub, map_nsmul, coordinateExponent_degree]

lemma fractionExponent_outside (s : ι →₀ ℕ) (k : ℕ) (i : ι)
    (hi : i ∉ Set.range a) : 0 ≤ fractionExponent a s k i := by
  simp [fractionExponent, coordinateExponent_outside a i hi]

/-- The exponent set for the requested integer degree piece. -/
def AllowedExponent (n : ℤ) :=
  {e : ι →₀ ℤ // e.degree = n ∧ ∀ i ∉ Set.range a, 0 ≤ e i}

/-- Every monomial fraction has an exponent in the prescribed set. -/
def monomialExponent (s : ι →₀ ℕ) (k : ℕ) :
    AllowedExponent a ((s.degree : ℤ) - k * (q + 1)) :=
  ⟨fractionExponent a s k, fractionExponent_degree a s k, fractionExponent_outside a s k⟩

/-- A uniform bound for the negative coordinates of one finite exponent. -/
def clearingPower (e : ι →₀ ℤ) : ℕ := e.support.sup fun i ↦ (-e i).toNat

lemma neg_le_clearingPower (e : ι →₀ ℤ) (i : ι) :
    -e i ≤ (clearingPower e : ℤ) := by
  classical
  by_cases hi : i ∈ e.support
  · exact (Int.self_le_toNat _).trans (by
      exact_mod_cast (Finset.le_sup (f := fun i ↦ (-e i).toNat) hi))
  · simp only [Finsupp.notMem_support_iff.mp hi, neg_zero]
    exact Nat.cast_nonneg _

lemma coordinateExponent_pos (j : Fin (q + 1)) : 1 ≤ coordinateExponent a (a j) := by
  classical
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    Nat.zero_le (Finsupp.single (a i) 1 (a j))) (Finset.mem_univ j)
  simpa only [coordinateExponent, Finsupp.finsetSum_apply, Finsupp.single_eq_same] using h

lemma clearedExponent_nonneg (n : ℤ) (e : AllowedExponent a n) (k : ℕ)
    (hk : clearingPower e.val ≤ k) (i : ι) :
    0 ≤ (e.val + k • exponentInt (coordinateExponent a)) i := by
  classical
  simp only [Finsupp.add_apply, Finsupp.smul_apply, exponentInt_apply, nsmul_eq_mul]
  by_cases hi : i ∈ Set.range a
  · obtain ⟨j, rfl⟩ := hi
    have hb := neg_le_clearingPower e.val (a j)
    have hc : (1 : ℤ) ≤ coordinateExponent a (a j) := by
      exact_mod_cast coordinateExponent_pos a j
    have hk' : (clearingPower e.val : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  · rw [coordinateExponent_outside a i hi]
    simpa using e.property.2 i hi

/-- A natural numerator exponent obtained by clearing a sufficiently large power. -/
def clearedNumerator (e : ι →₀ ℤ) (k : ℕ) : ι →₀ ℕ :=
  Finsupp.mapRange Int.toNat (by rfl) (e + k • exponentInt (coordinateExponent a))

lemma fractionExponent_cleared (n : ℤ) (e : AllowedExponent a n) (k : ℕ)
    (hk : clearingPower e.val ≤ k) :
    fractionExponent a (clearedNumerator a e.val k) k = e.val := by
  ext i
  change ((e.val + k • exponentInt (coordinateExponent a)) i).toNat -
    (k • exponentInt (coordinateExponent a)) i = e.val i
  rw [Int.toNat_of_nonneg (clearedExponent_nonneg a n e k hk i), Finsupp.add_apply]
  exact add_sub_cancel_right _ _

/-- Clearing the denominator also gives the required homogeneous numerator degree. -/
lemma clearedNumerator_degree (n : ℤ) (e : AllowedExponent a n) (k : ℕ)
    (hk : clearingPower e.val ≤ k) :
    ((clearedNumerator a e.val k).degree : ℤ) - k * (q + 1) = n := by
  rw [← fractionExponent_degree, fractionExponent_cleared a n e k hk]
  exact e.property.1

/-- Every finite collection of allowed exponents can use one denominator power. -/
lemma exists_common_denominator (n : ℤ) (S : Finset (AllowedExponent a n)) :
    ∃ k : ℕ, ∀ e ∈ S, ∃ s : ι →₀ ℕ,
      fractionExponent a s k = e.val ∧ (s.degree : ℤ) - k * (q + 1) = n := by
  classical
  refine ⟨S.sup (fun e ↦ clearingPower e.val), fun e he ↦ ?_⟩
  have hk := Finset.le_sup (f := fun e : AllowedExponent a n ↦ clearingPower e.val) he
  exact ⟨clearedNumerator a e.val _, fractionExponent_cleared a n e _ hk,
    clearedNumerator_degree a n e _ hk⟩

/-- Deleting an entry induces the inclusion of the corresponding exponent sets. -/
def exponentFace (q : ℕ) (b : Fin (q + 2) → ι) (k : Fin (q + 2)) (n : ℤ) :
    AllowedExponent (b ∘ k.succAbove) n ↪ AllowedExponent b n where
  toFun e := ⟨e.val, e.property.1, fun i hi ↦ e.property.2 i
    (fun ⟨j, hj⟩ ↦ hi ⟨k.succAbove j, hj⟩)⟩
  inj' _ _ h := Subtype.ext (congrArg (fun e : AllowedExponent b n ↦ e.val) h)

@[simp] lemma exponentFace_val (q : ℕ) (b : Fin (q + 2) → ι)
    (k : Fin (q + 2)) (n : ℤ) (e : AllowedExponent (b ∘ k.succAbove) n) :
    (exponentFace q b k n e).val = e.val := rfl

/-- The numerator adjustment in the actual face map preserves the integer exponent. -/
lemma fractionExponent_face (q : ℕ) (b : Fin (q + 2) → ι) (k : Fin (q + 2))
    (s : ι →₀ ℕ) (l : ℕ) :
    fractionExponent b (s + Finsupp.single (b k) l) l =
      fractionExponent (b ∘ k.succAbove) s l := by
  classical
  rw [fractionExponent, fractionExponent, coordinateExponent_face q b k]
  ext i
  simp only [map_add, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply,
    exponentInt_apply, Finsupp.single_apply, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

variable (R ι)

/-- Equal integer exponents give equal fractions, even over rings with zero divisors. -/
lemma monomialFraction_eq_of_exponent (s t : ι →₀ ℕ) (k l : ℕ)
    (h : fractionExponent a s k = fractionExponent a t l) (r : R) :
    fraction R ι a (monomial s r) k = fraction R ι a (monomial t r) l := by
  have he : l • coordinateExponent a + s = k • coordinateExponent a + t := by
    ext i
    have hi := congrArg (fun e : ι →₀ ℤ ↦ e i) h
    simp only [fractionExponent, Finsupp.sub_apply, Finsupp.smul_apply,
      exponentInt_apply, nsmul_eq_mul] at hi
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
    zify
    omega
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  change TwistCech.coordinateProduct R ι a ^ l * monomial s r =
    TwistCech.coordinateProduct R ι a ^ k * monomial t r
  simp only [coordinateProduct_eq_monomial, monomial_pow, one_pow,
    monomial_mul_monomial, one_mul, he]

/-- The concrete unit-coefficient monomial associated to an allowed integer exponent. -/
def integerMonomial (n : ℤ) (e : AllowedExponent a n) : piece R ι a n :=
  ⟨fraction R ι a (monomial (clearedNumerator a e.val (clearingPower e.val)) 1)
      (clearingPower e.val), by
    have hm := monomialFraction_mem R ι a
      (clearedNumerator a e.val (clearingPower e.val)) 1 (clearingPower e.val)
    simpa only [clearedNumerator_degree a n e _ le_rfl] using hm⟩

/-- Any representative of the same integer exponent gives the same concrete monomial. -/
lemma integerMonomial_eq (n : ℤ) (e : AllowedExponent a n) (s : ι →₀ ℕ) (k : ℕ)
    (h : fractionExponent a s k = e.val) :
    (integerMonomial R ι a n e : Full R ι a) = fraction R ι a (monomial s 1) k :=
  monomialFraction_eq_of_exponent R ι a _ s _ k
    ((fractionExponent_cleared a n e _ le_rfl).trans h.symm) 1

/-- Finite integer-monomial combinations map linearly to the actual degree piece. -/
def monomialPresentation (n : ℤ) : (AllowedExponent a n →₀ R) →ₗ[R] piece R ι a n :=
  Finsupp.linearCombination R (integerMonomial R ι a n)

/-- A finite combination is represented by the numerator at any common clearing power. -/
lemma monomialPresentation_common (n : ℤ) (x : AllowedExponent a n →₀ R) (k : ℕ)
    (hk : ∀ e ∈ x.support, clearingPower e.val ≤ k) :
    (monomialPresentation R ι a n x : Full R ι a) =
      fraction R ι a (x.sum fun e r ↦ monomial (clearedNumerator a e.val k) r) k := by
  classical
  change ((Finsupp.linearCombination R (integerMonomial R ι a n)) x : Full R ι a) = _
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]
  rw [show fraction R ι a (∑ e ∈ x.support, monomial (clearedNumerator a e.val k) (x e)) k =
    ∑ e ∈ x.support, fraction R ι a (monomial (clearedNumerator a e.val k) (x e)) k from
      map_sum (fractionLinear R ι a k) _ _]
  apply Finset.sum_congr rfl
  intro e he
  rw [integerMonomial_eq R ι a n e _ k (fractionExponent_cleared a n e k (hk e he)),
    fraction_smul, ← (monomial _).map_smul]
  simp only [smul_eq_mul, mul_one]

/-- The integer-monomial presentation is surjective onto the concrete degree piece. -/
lemma monomialPresentation_surjective (n : ℤ) :
    Function.Surjective (monomialPresentation R ι a n) := by
  classical
  let F := (piece R ι a n).subtype.comp (monomialPresentation R ι a n)
  have hr : piece R ι a n ≤ LinearMap.range F := by
    rw [piece_eq_span_monomial]
    apply Submodule.span_le.mpr
    rintro x ⟨s, k, hn, rfl⟩
    let e : AllowedExponent a n := ⟨fractionExponent a s k,
      (fractionExponent_degree a s k).trans hn, fractionExponent_outside a s k⟩
    refine ⟨Finsupp.single e 1, ?_⟩
    change (monomialPresentation R ι a n (Finsupp.single e 1) : Full R ι a) = _
    simp only [monomialPresentation, Finsupp.linearCombination_single, one_smul]
    exact integerMonomial_eq R ι a n e s k rfl
  intro x
  obtain ⟨z, hz⟩ := hr x.property
  exact ⟨z, Subtype.ext hz⟩

/-- Restriction of a monomial fraction is the explicit numerator adjustment. -/
lemma fullFace_monomial (q : ℕ) (b : Fin (q + 2) → ι) (k : Fin (q + 2))
    (s : ι →₀ ℕ) (r : R) (l : ℕ) :
    fullFace R ι q b k (fraction R ι (b ∘ k.succAbove) (monomial s r) l) =
      fraction R ι b (monomial (s + Finsupp.single (b k) l) r) l := by
  rw [fullFace_fraction, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

/-- The actual degree-piece face map is exponent inclusion on integer monomials. -/
lemma faceLinear_integerMonomial (q : ℕ) (b : Fin (q + 2) → ι)
    (k : Fin (q + 2)) (n : ℤ) (e : AllowedExponent (b ∘ k.succAbove) n) :
    faceLinear R ι q b k n (integerMonomial R ι (b ∘ k.succAbove) n e) =
      integerMonomial R ι b n (exponentFace q b k n e) := by
  let s := clearedNumerator (b ∘ k.succAbove) e.val (clearingPower e.val)
  let l := clearingPower e.val
  have hs : fractionExponent (b ∘ k.succAbove) s l = e.val :=
    fractionExponent_cleared (b ∘ k.succAbove) n e l le_rfl
  apply Subtype.ext
  change fullFace R ι q b k (integerMonomial R ι (b ∘ k.succAbove) n e).val = _
  rw [integerMonomial_eq R ι (b ∘ k.succAbove) n e s l hs, fullFace_monomial]
  exact (integerMonomial_eq R ι b n (exponentFace q b k n e)
    (s + Finsupp.single (b k) l) l ((fractionExponent_face q b k s l).trans hs)).symm

/-- The entire presentation commutes with the actual face map by exponent inclusion. -/
lemma monomialPresentation_face (q : ℕ) (b : Fin (q + 2) → ι)
    (k : Fin (q + 2)) (n : ℤ) :
    (monomialPresentation R ι b n).comp (Finsupp.lmapDomain R R (exponentFace q b k n)) =
      (faceLinear R ι q b k n).comp (monomialPresentation R ι (b ∘ k.succAbove) n) :=
  Finsupp.lmapDomain_linearCombination R (exponentFace q b k n) (faceLinear R ι q b k n)
    (faceLinear_integerMonomial R ι q b k n)

/-- Polynomial exponents included in the additive group algebra of integer exponents. -/
def polynomialLaurent : MvPolynomial ι R →+* AddMonoidAlgebra R (ι →₀ ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom R exponentInt

@[simp] lemma polynomialLaurent_monomial (s : ι →₀ ℕ) (r : R) :
    polynomialLaurent R ι (monomial s r) = AddMonoidAlgebra.single (exponentInt s) r :=
  AddMonoidAlgebra.mapDomain_single

lemma polynomialLaurent_inverse :
    polynomialLaurent R ι (TwistCech.coordinateProduct R ι a) *
      AddMonoidAlgebra.single (-exponentInt (coordinateExponent a)) 1 = 1 := by
  rw [coordinateProduct_eq_monomial, polynomialLaurent_monomial]
  simp [AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def]

/-- The concrete localization maps to integer Laurent polynomials. -/
def laurentMap : Full R ι a →+* AddMonoidAlgebra R (ι →₀ ℤ) :=
  Localization.awayLift (polynomialLaurent R ι) (TwistCech.coordinateProduct R ι a)
    (isUnit_iff_exists_inv.mpr ⟨_, polynomialLaurent_inverse R ι a⟩)

lemma laurentMap_monomial (s : ι →₀ ℕ) (r : R) (k : ℕ) :
    laurentMap R ι a (fraction R ι a (monomial s r) k) =
      AddMonoidAlgebra.single (fractionExponent a s k) r := by
  rw [laurentMap, fraction,
    Localization.awayLift_mk (hv := polynomialLaurent_inverse R ι a)]
  simp only [polynomialLaurent_monomial, AddMonoidAlgebra.single_pow, one_pow,
    AddMonoidAlgebra.single_mul_single, mul_one, smul_neg, ← sub_eq_add_neg,
    fractionExponent]

/-- Coefficient extraction on the full localization is linear over the base ring. -/
def laurentLinear : Full R ι a →ₗ[R] (ι →₀ ℤ) →₀ R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap.comp
    (show Full R ι a →ₐ[R] AddMonoidAlgebra R (ι →₀ ℤ) from
      { laurentMap R ι a with
        commutes' := fun r ↦ by
          change laurentMap R ι a (algebraMap (MvPolynomial ι R) _ (C r)) = _
          rw [laurentMap, IsLocalization.Away.lift_eq]
          change polynomialLaurent R ι (monomial 0 r) = AddMonoidAlgebra.single 0 r
          rw [polynomialLaurent_monomial, map_zero] }).toLinearMap

lemma laurentLinear_integerMonomial (n : ℤ) (e : AllowedExponent a n) :
    laurentLinear R ι a (integerMonomial R ι a n e) = Finsupp.single e.val 1 := by
  change (laurentMap R ι a (fraction R ι a _ _)).coeff = _
  rw [laurentMap_monomial, fractionExponent_cleared a n e _ le_rfl]
  rfl

/-- Coefficients of an arbitrary fraction are obtained by shifting numerator exponents. -/
lemma laurentLinear_fraction (f : MvPolynomial ι R) (k : ℕ) :
    laurentLinear R ι a (fraction R ι a f k) =
      Finsupp.mapDomain (fun s ↦ fractionExponent a s k) f.coeff := by
  classical
  rw [fraction_eq_sum, map_sum]
  change (∑ s ∈ f.support, (laurentMap R ι a (fraction R ι a (monomial s (f.coeff s)) k)).coeff)
    = _
  simp only [laurentMap_monomial, AddMonoidAlgebra.coeff_single]
  rfl

/-- Laurent coefficients recover the input finite combination by exponent inclusion. -/
lemma laurentLinear_presentation (n : ℤ) :
    ((laurentLinear R ι a).comp (piece R ι a n).subtype).comp
        (monomialPresentation R ι a n) =
      Finsupp.lmapDomain R R (fun e : AllowedExponent a n ↦ e.val) := by
  apply Finsupp.lhom_ext
  intro e r
  simp only [LinearMap.comp_apply, monomialPresentation, Finsupp.linearCombination_single,
    Submodule.subtype_apply, map_smul, laurentLinear_integerMonomial,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.smul_single,
    smul_eq_mul, mul_one]

/-- Integer-monomial coefficients are unique over every commutative base ring. -/
lemma monomialPresentation_injective (n : ℤ) :
    Function.Injective (monomialPresentation R ι a n) := by
  intro x y h
  apply Finsupp.mapDomain_injective Subtype.val_injective
  have hc := congrArg (fun z : piece R ι a n ↦ laurentLinear R ι a z) h
  exact (LinearMap.congr_fun (laurentLinear_presentation R ι a n) x).symm.trans
    (hc.trans (LinearMap.congr_fun (laurentLinear_presentation R ι a n) y))

/-- Extract the coefficients at the allowed exponents of a concrete degree-piece element. -/
def monomialCoefficients (n : ℤ) : piece R ι a n →ₗ[R] (AllowedExponent a n →₀ R) :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    ((laurentLinear R ι a).comp (piece R ι a n).subtype)

@[simp] lemma monomialCoefficients_apply (n : ℤ) (x : piece R ι a n)
    (e : AllowedExponent a n) :
    monomialCoefficients R ι a n x e = laurentLinear R ι a x e.val := rfl

/-- Coefficient extraction is a left inverse to the denominator-clearing presentation. -/
lemma monomialCoefficients_presentation (n : ℤ) (x : AllowedExponent a n →₀ R) :
    monomialCoefficients R ι a n (monomialPresentation R ι a n x) = x := by
  change Finsupp.lcomapDomain (R := R) Subtype.val Subtype.val_injective
    ((((laurentLinear R ι a).comp (piece R ι a n).subtype).comp
      (monomialPresentation R ι a n)) x) = x
  rw [laurentLinear_presentation]
  exact Finsupp.comapDomain_mapDomain Subtype.val Subtype.val_injective x

/-- Reassembling the extracted coefficients returns the original concrete fraction. -/
lemma monomialPresentation_coefficients (n : ℤ) (x : piece R ι a n) :
    monomialPresentation R ι a n (monomialCoefficients R ι a n x) = x := by
  obtain ⟨y, rfl⟩ := monomialPresentation_surjective R ι a n x
  rw [monomialCoefficients_presentation]

/-- The integer-monomial basis presentation of the actual localization degree piece. -/
def monomialEquiv (n : ℤ) : (AllowedExponent a n →₀ R) ≃ₗ[R] piece R ι a n where
  __ := monomialPresentation R ι a n
  invFun := monomialCoefficients R ι a n
  left_inv := monomialCoefficients_presentation R ι a n
  right_inv := monomialPresentation_coefficients R ι a n

/-- Under the equivalence the actual face map is inclusion of exponent sets. -/
lemma monomialEquiv_face (q : ℕ) (b : Fin (q + 2) → ι) (k : Fin (q + 2)) (n : ℤ)
    (x : AllowedExponent (b ∘ k.succAbove) n →₀ R) :
    faceLinear R ι q b k n (monomialEquiv R ι (b ∘ k.succAbove) n x) =
      monomialEquiv R ι b n (Finsupp.mapDomain (exponentFace q b k n) x) :=
  (LinearMap.congr_fun (monomialPresentation_face R ι q b k n) x).symm

end FLT.Mazur.ProjectiveSpace.LocalizationDegree
