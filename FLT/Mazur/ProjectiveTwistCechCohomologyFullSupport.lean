/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyDeletion

/-!
# Cohomology of full-support tuple cochains

Deletion and insertion give the cohomology of the unbounded full-support
complex over an arbitrary commutative ring. In particular, vanishing above the
top degree follows from the connecting isomorphisms, without truncating tuples.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

variable (R : Type u) [CommRing R] (ι : Type u)

section Insertion

variable (S : Set ι) (j : ι)
variable (h : ∀ (q : ℕ) (a : Fin (q + 1) → ι),
  S ⊆ Set.range (Fin.cons j a) → S ⊆ Set.range a)

/-- Inserting a vertex gives a homotopy whenever it preserves support. -/
def supportHomotopy (q : ℕ) :
    supportTerm R ι S (q + 1) →ₗ[R] supportTerm R ι S q where
  toFun x := ⟨fun a ↦ x.val (Fin.cons j a),
    fun a ha ↦ x.property _ (fun hs ↦ ha (h q a hs))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The insertion identity holds in every positive degree, including repeated tuples. -/
lemma supportHomotopy_identity (q : ℕ) (x : supportTerm R ι S (q + 1)) :
    supportHomotopy R ι S j h (q + 1) (supportDifferential R ι S (q + 1) x) +
      supportDifferential R ι S q (supportHomotopy R ι S j h q x) = x := by
  apply Subtype.ext
  funext a
  change (∑ k : Fin (q + 3), (-1 : ℤ) ^ (k : ℕ) •
      x.val (Fin.cons j a ∘ k.succAbove)) +
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      x.val (Fin.cons j (a ∘ k.succAbove))) = x.val a
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Finset.sum_neg_distrib]
  change x.val a + -(∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
    x.val (Fin.cons j (a ∘ k.succAbove))) +
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      x.val (Fin.cons j (a ∘ k.succAbove))) = x.val a
  abel

include h in
/-- Insertion proves positive-degree exactness of the actual supported complex. -/
lemma support_exactAt_succ (q : ℕ) : (supportComplex R ι S).ExactAt (q + 1) := by
  rw [(supportComplex R ι S).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hd : supportDifferential R ι S (q + 1) x = 0 := by
    simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
      supportComplex, CochainComplex.of.d] using hx
  refine ⟨supportHomotopy R ι S j h q x, ?_⟩
  have hh := supportHomotopy_identity R ι S j h q x
  simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    supportComplex, CochainComplex.of.d, hd] using hh

end Insertion

/-- A vertex outside the support can always be inserted. -/
lemma support_insert_outside (S : Set ι) (j : ι) (hj : j ∉ S)
    (q : ℕ) (a : Fin (q + 1) → ι) :
    S ⊆ Set.range (Fin.cons j a) → S ⊆ Set.range a := by
  intro hs i hi
  have hr := hs hi
  rw [Fin.range_cons, Set.mem_insert_iff] at hr
  exact hr.resolve_left (fun hij ↦ hj (hij ▸ hi))

/-- Every supported zero-cocycle is constant on singleton tuples. -/
lemma support_zero_cocycle_constant (S : Set ι) (j : ι) (x : supportTerm R ι S 0)
    (hx : supportDifferential R ι S 0 x = 0) (a : Fin 1 → ι) :
    x.val a = x.val (fun _ ↦ j) := by
  have hh := congrArg (fun z : supportTerm R ι S 1 ↦ z.val (Fin.cons j a)) hx
  change (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    x.val (Fin.cons j a ∘ k.succAbove)) = 0 at hh
  have he : Fin.cons j a ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ j := by
    ext k
    fin_cases k
    rfl
  rw [Fin.sum_univ_two] at hh
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.val_one, pow_one, neg_one_zsmul, he] at hh
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)

/-- Nonempty support avoiding a vertex has zero cohomology in every degree. -/
lemma support_isZero_homology_outside (S : Set ι) (j : ι) (hj : j ∉ S)
    (hS : S.Nonempty) (q : ℕ) : IsZero ((supportComplex R ι S).homology q) := by
  cases q with
  | succ q =>
    exact (support_exactAt_succ R ι S j (support_insert_outside ι S j hj) q).isZero_homology
  | zero =>
    apply HomologicalComplex.ExactAt.isZero_homology
    rw [(supportComplex R ι S).exactAt_iff' 0 0 1 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hd : supportDifferential R ι S 0 x = 0 := by
      simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        supportComplex, CochainComplex.of.d] using hx
    have hz : x = 0 := by
      apply Subtype.ext
      funext a
      rw [support_zero_cocycle_constant R ι S j x hd a]
      apply x.property
      intro hs
      obtain ⟨i, hi⟩ := hS
      obtain ⟨k, hk⟩ := hs hi
      apply hj
      change j = i at hk
      rw [hk]
      exact hi
    exact ⟨0, by simp [hz]⟩

/-- The connecting map is an isomorphism when the weakened support stays nonempty. -/
def deletionHomologyIso (S : Set ι) (j : ι) (hj : j ∈ S)
    (hS : (S \ {j}).Nonempty) (q : ℕ) :
    (supportComplex R (DeletedIndex ι j) (Subtype.val ⁻¹' S)).homology q ≅
      (supportComplex R ι S).homology (q + 1) :=
  (deletion_shortExact R ι S j hj).δIso q (q + 1) rfl
    (support_isZero_homology_outside R ι (S \ {j}) j (by simp) hS q)
    (support_isZero_homology_outside R ι (S \ {j}) j (by simp) hS (q + 1))

/-- A full-support cochain is zero below the top degree. -/
lemma fullSupport_term_eq_zero [Fintype ι] (q : ℕ) (hq : q + 1 < Fintype.card ι)
    (x : supportTerm R ι Set.univ q) : x = 0 := by
  apply Subtype.ext
  funext a
  apply x.property
  intro hs
  have hc := Fintype.card_le_of_surjective a (fun i ↦ hs (Set.mem_univ i))
  simp only [Fintype.card_fin] at hc
  omega

/-- Below-top vanishing, including degree zero in the induction step. -/
lemma fullSupport_isZero_below [Fintype ι] (q : ℕ) (hq : q + 1 < Fintype.card ι) :
    IsZero ((supportComplex R ι Set.univ).homology q) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y ↦ (fullSupport_term_eq_zero R ι q hq x).trans
    (fullSupport_term_eq_zero R ι q hq y).symm⟩

section Singleton

variable [Subsingleton ι] (j : ι)

/-- Every nonempty tuple on one index has full support. -/
lemma singleton_fullSupport (q : ℕ) (a : Fin (q + 1) → ι) :
    (Set.univ : Set ι) ⊆ Set.range a :=
  fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- Evaluation identifies singleton-index cochains with the coefficient ring. -/
def singletonTermEquiv (q : ℕ) : supportTerm R ι Set.univ q ≃ₗ[R] R where
  toFun x := x.val (fun _ ↦ j)
  invFun r := ⟨fun _ ↦ r, fun a ha ↦ False.elim (ha (singleton_fullSupport ι q a))⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact congrArg x.val (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The first differential on one index is zero, computed on its two faces. -/
lemma singleton_d_zero : (supportComplex R ι Set.univ).d 0 1 = 0 := by
  simp only [supportComplex]
  ext x a
  change (∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • x.val (a ∘ k.succAbove)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul]
  rw [show a ∘ (0 : Fin 2).succAbove = a ∘ (1 : Fin 2).succAbove from
    Subsingleton.elim _ _]
  exact add_neg_cancel _

/-- The singleton base case computes categorical degree-zero homology R-linearly. -/
def singletonHomologyIso : (supportComplex R ι Set.univ).homology 0 ≅ ModuleCat.of R R :=
  (ShortComplex.HomologyData.ofZeros ((supportComplex R ι Set.univ).sc 0)
    (by
      simp [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
        HomologicalComplex.shortComplexFunctor', supportComplex, CochainComplex.of.d])
    (by
      change (supportComplex R ι Set.univ).d 0 ((ComplexShape.up ℕ).next 0) = 0
      rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl)]
      exact singleton_d_zero R ι)).left.homologyIso ≪≫
    (singletonTermEquiv R ι j 0).toModuleIso

include j in
/-- Insertion on a singleton gives vanishing in all positive degrees. -/
lemma singleton_isZero_succ (q : ℕ) :
    IsZero ((supportComplex R ι Set.univ).homology (q + 1)) :=
  (support_exactAt_succ R ι Set.univ j
    (fun q a _ ↦ singleton_fullSupport ι q a) q).isZero_homology

end Singleton

/-- Full-support cohomology is R at the top and zero in every other degree. -/
theorem fullSupport_computation [Fintype ι] [Nonempty ι] :
    Nonempty ((supportComplex R ι Set.univ).homology (Fintype.card ι - 1) ≅
      ModuleCat.of R R) ∧
    ∀ q : ℕ, q ≠ Fintype.card ι - 1 →
      IsZero ((supportComplex R ι Set.univ).homology q) := by
  classical
  generalize hk : Fintype.card ι = k
  induction k using Nat.strong_induction_on generalizing ι with
  | h k ih =>
    have hkpos : 0 < k := hk ▸ Fintype.card_pos
    let j : ι := Classical.choice inferInstance
    by_cases hkone : k = 1
    · have oneIndex : Subsingleton ι :=
        Fintype.card_le_one_iff_subsingleton.mp (by omega)
      rw [hkone]
      refine ⟨⟨singletonHomologyIso R ι j⟩, ?_⟩
      intro q hq
      cases q with
      | zero => exact False.elim (hq rfl)
      | succ q => exact singleton_isZero_succ R ι j q
    · have hcard : Fintype.card (DeletedIndex ι j) = k - 1 := by
        simp only [DeletedIndex, Ne, Fintype.card_subtype_compl,
          Fintype.card_subtype_eq, hk]
      have deletedNonempty : Nonempty (DeletedIndex ι j) :=
        Fintype.card_pos_iff.mp (by omega)
      obtain ⟨htop, hvanish⟩ := ih (k - 1) (by omega) (DeletedIndex ι j) hcard
      have hS : (Set.univ \ {j}).Nonempty := by
        obtain ⟨i⟩ := deletedNonempty
        exact ⟨i.val, Set.mem_univ _, i.property⟩
      have hshift (q : ℕ) :
          (supportComplex R (DeletedIndex ι j) Set.univ).homology q ≅
            (supportComplex R ι Set.univ).homology (q + 1) := by
        simpa only [Set.preimage_univ] using
          deletionHomologyIso R ι Set.univ j (Set.mem_univ j) hS q
      constructor
      · obtain ⟨etop⟩ := htop
        have hdeg : k - 1 - 1 + 1 = k - 1 := by omega
        exact ⟨by simpa only [hdeg] using (hshift (k - 1 - 1)).symm ≪≫ etop⟩
      · intro q hq
        cases q with
        | zero => exact fullSupport_isZero_below R ι 0 (by omega)
        | succ q =>
          exact (hvanish q (by omega)).of_iso (hshift q).symm

/-- The top cohomology comparison is linear over the arbitrary base ring. -/
def fullSupportHomologyIso [Fintype ι] [Nonempty ι] :
    (supportComplex R ι Set.univ).homology (Fintype.card ι - 1) ≅ ModuleCat.of R R :=
  (fullSupport_computation R ι).1.some

/-- All degrees away from the top vanish, with no upper bound on the degree. -/
lemma fullSupport_isZero_homology [Fintype ι] [Nonempty ι] (q : ℕ)
    (hq : q ≠ Fintype.card ι - 1) :
    IsZero ((supportComplex R ι Set.univ).homology q) :=
  (fullSupport_computation R ι).2 q hq

/-- An all-negative exponent has the full-support tuple complex. -/
def negativeExponentSupportIso (n : ℤ) (e : ι →₀ ℤ) (he : e.degree = n)
    (hneg : ∀ i, e i < 0) :
    TwistGradedCech.exponentComplex R ι n e ≅ supportComplex R ι Set.univ :=
  exponentSupportIso R ι n e he ≪≫
    eqToIso (congrArg (supportComplex R ι) (Set.eq_univ_of_forall hneg))

/-- Top cohomology of the actual all-negative exponent summand is R. -/
def negativeExponentHomologyIso [Fintype ι] [Nonempty ι]
    (n : ℤ) (e : ι →₀ ℤ) (he : e.degree = n) (hneg : ∀ i, e i < 0) :
    (TwistGradedCech.exponentComplex R ι n e).homology (Fintype.card ι - 1) ≅
      ModuleCat.of R R :=
  HomologicalComplex.homologyMapIso (negativeExponentSupportIso R ι n e he hneg) _ ≪≫
    fullSupportHomologyIso R ι

/-- The actual all-negative exponent summand vanishes in every other degree. -/
lemma negativeExponent_isZero_homology [Fintype ι] [Nonempty ι]
    (n : ℤ) (e : ι →₀ ℤ) (he : e.degree = n) (hneg : ∀ i, e i < 0)
    (q : ℕ) (hq : q ≠ Fintype.card ι - 1) :
    IsZero ((TwistGradedCech.exponentComplex R ι n e).homology q) :=
  (fullSupport_isZero_homology R ι q hq).of_iso
    (HomologicalComplex.homologyMapIso (negativeExponentSupportIso R ι n e he hneg) q)

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
