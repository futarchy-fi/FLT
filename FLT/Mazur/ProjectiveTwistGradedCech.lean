/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationDegreeMonomial
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The graded Cech complex of projective twists

The actual twisting-sheaf Cech terms carry their constant base-ring action.
Multiplying first-chart coefficients by the chart variable to the twist degree
identifies this complex with products of homogeneous localization pieces.
The differential is the alternating localization map: chart transitions cancel.
Integer-monomial coordinates expose its exponent summands for further computation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace.TwistGradedCech

open LocalizationDegree

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The base-ring module structure on the actual categorical terms. -/
instance termModule (n : ℤ) (q : ℕ) : Module R ((TwistCech.complex R ι n).X q) :=
  (TwistCech.termEquiv R ι n q).module R

/-- First-chart coefficient evaluation is linear over the base ring. -/
def coefficientLinearEquiv (n : ℤ) (q : ℕ) :
    (TwistCech.complex R ι n).X q ≃ₗ[R]
      (∀ a : Fin (q + 1) → ι, TwistCech.intersectionRing R ι a) :=
  (TwistCech.termEquiv R ι n q).linearEquiv R

/-- The transferred action is exactly multiplication on the original sheaf. -/
lemma smul_eq_termScalar (n : ℤ) (q : ℕ) (r : R)
    (x : (TwistCech.complex R ι n).X q) :
    r • x = termScalar R ι n q r x := by
  apply (coefficientLinearEquiv R ι n q).injective
  rw [map_smul]
  funext a
  exact (termEquiv_scalar R ι n q r x a).symm

/-- Products of the concrete integer-degree pieces of the full localizations. -/
abbrev Term (n : ℤ) (q : ℕ) := ∀ a : Fin (q + 1) → ι, piece R ι a n

/-- The graded term comparison uses the actual sheaf evaluation and chart shift. -/
def termLinearEquiv (n : ℤ) (q : ℕ) :
    (TwistCech.complex R ι n).X q ≃ₗ[R] Term R ι n q :=
  (coefficientLinearEquiv R ι n q).trans (LinearEquiv.piCongrRight fun a ↦
    (zeroEquiv R ι a).trans (shift R ι a 0 n))

lemma termLinearEquiv_apply (n : ℤ) (q : ℕ)
    (x : (TwistCech.complex R ι n).X q) (a : Fin (q + 1) → ι) :
    termLinearEquiv R ι n q x a =
      shift R ι a 0 n (zeroEquiv R ι a (TwistCech.termEquiv R ι n q x a)) := rfl

/-- Shifting absorbs precisely the face's change-of-chart coefficient. -/
lemma shift_face (n : ℤ) (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2))
    (x : TwistCech.intersectionRing R ι (a ∘ k.succAbove)) :
    shift R ι a 0 n (zeroEquiv R ι a
      (TwistCech.faceRingCoefficient R ι n q a k * TwistCech.faceRingMap R ι q a k x)) =
      faceLinear R ι q a k n (shift R ι (a ∘ k.succAbove) 0 n
        (zeroEquiv R ι (a ∘ k.succAbove) x)) := by
  apply (shift R ι a 0 n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [face_shift_coefficient, zeroEquiv_val, zeroEquiv_val,
    HomogeneousLocalization.val_mul, fullFace_zero]

/-- Each graded coface is the canonical degree-preserving localization map. -/
lemma termLinearEquiv_coface (n : ℤ) (q : ℕ) (k : Fin (q + 2))
    (x : (TwistCech.complex R ι n).X q) (a : Fin (q + 2) → ι) :
    termLinearEquiv R ι n (q + 1) (TwistCech.coface R ι n q k x) a =
      faceLinear R ι q a k n (termLinearEquiv R ι n q x (a ∘ k.succAbove)) := by
  rw [termLinearEquiv_apply, TwistCech.termEquiv_coface, shift_face]
  rfl

/-- The differential is the alternating sum of degree-n localization maps. -/
lemma differential_localizations (n : ℤ) (q : ℕ)
    (x : (TwistCech.complex R ι n).X q) (a : Fin (q + 2) → ι) :
    termLinearEquiv R ι n (q + 1) ((TwistCech.complex R ι n).d q (q + 1) x) a =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        faceLinear R ι q a k n (termLinearEquiv R ι n q x (a ∘ k.succAbove)) := by
  rw [termLinearEquiv_apply, TwistCech.differential_localizations, map_sum, map_sum]
  simp only [map_zsmul, shift_face, termLinearEquiv_apply]

/-- The explicit graded differential, defined without chart transition factors. -/
def differential (n : ℤ) (q : ℕ) : Term R ι n q →ₗ[R] Term R ι n (q + 1) :=
  LinearMap.pi fun a ↦ ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
    (faceLinear R ι q a k n).comp (LinearMap.proj (a ∘ k.succAbove))

lemma differential_apply (n : ℤ) (q : ℕ) (x : Term R ι n q) (a : Fin (q + 2) → ι) :
    differential R ι n q x a = ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      faceLinear R ι q a k n (x (a ∘ k.succAbove)) := by
  simp [differential]

/-- Compatibility of the actual sheaf differential with the explicit graded one. -/
lemma termLinearEquiv_d (n : ℤ) (q : ℕ) (x : (TwistCech.complex R ι n).X q) :
    termLinearEquiv R ι n (q + 1) ((TwistCech.complex R ι n).d q (q + 1) x) =
      differential R ι n q (termLinearEquiv R ι n q x) := by
  funext a
  exact (differential_localizations R ι n q x a).trans
    (differential_apply R ι n q _ a).symm

/-- The actual sheaf differential respects the constant base-ring action. -/
def sheafDifferential (n : ℤ) (p q : ℕ) :
    (TwistCech.complex R ι n).X p →ₗ[R] (TwistCech.complex R ι n).X q where
  __ := ((TwistCech.complex R ι n).d p q).hom
  map_smul' r x := by
    simp only [RingHom.id_apply, smul_eq_termScalar]
    exact (ConcreteCategory.congr_hom
      (((cechComplexFunctor (chart R ι)).map
        (moduleMultiply (twistingSheaf R ι n) (constantSection R ι ⊤ r)).hom).comm p q)
      x)

/-- The original Cech complex with its canonical base-ring module structure. -/
def sheafComplex (n : ℤ) : CochainComplex (ModuleCat R) ℕ where
  X q := ModuleCat.of R ((TwistCech.complex R ι n).X q)
  d p q := ModuleCat.ofHom (sheafDifferential R ι n p q)
  shape p q h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom ((TwistCech.complex R ι n).shape p q h) x
  d_comp_d' p q s _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom ((TwistCech.complex R ι n).d_comp_d p q s) x

/-- Forgetting scalars recovers the actual categorical sheaf Cech complex. -/
def forgetSheafComplexIso (n : ℤ) :
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (sheafComplex R ι n) ≅ TwistCech.complex R ι n :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ by
    ext x
    rfl)

/-- The explicit localization differential squares to zero. -/
lemma differential_sq (n : ℤ) (q : ℕ) (x : Term R ι n q) :
    differential R ι n (q + 1) (differential R ι n q x) = 0 := by
  obtain ⟨y, rfl⟩ := (termLinearEquiv R ι n q).surjective x
  rw [← termLinearEquiv_d, ← termLinearEquiv_d]
  have h := ConcreteCategory.congr_hom ((TwistCech.complex R ι n).d_comp_d
    q (q + 1) (q + 1 + 1)) y
  change (TwistCech.complex R ι n).d (q + 1) (q + 1 + 1)
    ((TwistCech.complex R ι n).d q (q + 1) y) = 0 at h
  rw [h, map_zero]

/-- The graded localization Cech complex with the alternating face differential. -/
def gradedComplex (n : ℤ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (Term R ι n q))
    (fun q ↦ ModuleCat.ofHom (differential R ι n q)) (fun q ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact differential_sq R ι n q x)

/-- The R-linear chain isomorphism from the actual twisting-sheaf Cech complex. -/
def gradedIso (n : ℤ) : sheafComplex R ι n ≅ gradedComplex R ι n :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (termLinearEquiv R ι n q).toModuleIso)
    (fun p q h ↦ by
      obtain rfl : p + 1 = q := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [gradedComplex, CochainComplex.of_d]
      change differential R ι n p (termLinearEquiv R ι n p x) = _
      exact (termLinearEquiv_d R ι n p x).symm)

/-- The isomorphism's components are the specified sheaf evaluation and shift maps. -/
lemma gradedIso_hom_apply (n : ℤ) (q : ℕ) (x : (TwistCech.complex R ι n).X q)
    (a : Fin (q + 1) → ι) :
    (gradedIso R ι n).hom.f q x a =
      shift R ι a 0 n (zeroEquiv R ι a (TwistCech.termEquiv R ι n q x a)) := rfl

/-- Monomial coordinates, with finite support separately on each tuple. -/
abbrev MonomialTerm (n : ℤ) (q : ℕ) :=
  ∀ a : Fin (q + 1) → ι, AllowedExponent a n →₀ R

/-- Concrete integer-monomial coordinates on each graded term. -/
def monomialTermEquiv (n : ℤ) (q : ℕ) :
    Term R ι n q ≃ₗ[R] MonomialTerm R ι n q :=
  LinearEquiv.piCongrRight fun a ↦ (monomialEquiv R ι a n).symm

/-- Monomial coordinates of the actual twisting-sheaf term. -/
def sheafMonomialEquiv (n : ℤ) (q : ℕ) :
    (TwistCech.complex R ι n).X q ≃ₗ[R] MonomialTerm R ι n q :=
  (termLinearEquiv R ι n q).trans (monomialTermEquiv R ι n q)

/-- The monomial differential is the alternating inclusion of exponent sets. -/
def monomialDifferential (n : ℤ) (q : ℕ) :
    MonomialTerm R ι n q →ₗ[R] MonomialTerm R ι n (q + 1) :=
  LinearMap.pi fun a ↦ ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
    (Finsupp.lmapDomain R R (exponentFace q a k n)).comp
      (LinearMap.proj (a ∘ k.succAbove))

lemma monomialDifferential_apply (n : ℤ) (q : ℕ) (x : MonomialTerm R ι n q)
    (a : Fin (q + 2) → ι) :
    monomialDifferential R ι n q x a =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        Finsupp.mapDomain (exponentFace q a k n) (x (a ∘ k.succAbove)) := by
  simp [monomialDifferential]

/-- The graded differential preserves every integer-exponent summand. -/
lemma monomialTermEquiv_d (n : ℤ) (q : ℕ) (x : Term R ι n q) :
    monomialTermEquiv R ι n (q + 1) (differential R ι n q x) =
      monomialDifferential R ι n q (monomialTermEquiv R ι n q x) := by
  funext a
  apply (monomialEquiv R ι a n).injective
  change monomialEquiv R ι a n ((monomialEquiv R ι a n).symm _) = _
  rw [LinearEquiv.apply_symm_apply, differential_apply, monomialDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, ← monomialEquiv_face]
  simp only [monomialTermEquiv, LinearEquiv.piCongrRight_apply,
    LinearEquiv.apply_symm_apply]

/-- In monomial coordinates the actual sheaf differential has only alternating inclusions. -/
lemma sheafMonomialEquiv_d (n : ℤ) (q : ℕ)
    (x : (TwistCech.complex R ι n).X q) :
    sheafMonomialEquiv R ι n (q + 1) ((TwistCech.complex R ι n).d q (q + 1) x) =
      monomialDifferential R ι n q (sheafMonomialEquiv R ι n q x) := by
  change monomialTermEquiv R ι n (q + 1) (termLinearEquiv R ι n (q + 1) _) = _
  rw [termLinearEquiv_d, monomialTermEquiv_d]
  rfl

/-- The monomial differential also squares to zero. -/
lemma monomialDifferential_sq (n : ℤ) (q : ℕ) (x : MonomialTerm R ι n q) :
    monomialDifferential R ι n (q + 1) (monomialDifferential R ι n q x) = 0 := by
  obtain ⟨y, rfl⟩ := (monomialTermEquiv R ι n q).surjective x
  rw [← monomialTermEquiv_d, ← monomialTermEquiv_d, differential_sq, map_zero]

/-- The Cech complex written entirely in integer-monomial coordinates. -/
def monomialComplex (n : ℤ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (MonomialTerm R ι n q))
    (fun q ↦ ModuleCat.ofHom (monomialDifferential R ι n q)) (fun q ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact monomialDifferential_sq R ι n q x)

/-- Integer-monomial coordinates give a second explicit chain isomorphism. -/
def monomialIso (n : ℤ) : gradedComplex R ι n ≅ monomialComplex R ι n :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (monomialTermEquiv R ι n q).toModuleIso)
    (fun p q h ↦ by
      obtain rfl : p + 1 = q := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [gradedComplex, monomialComplex, CochainComplex.of_d]
      change monomialDifferential R ι n p (monomialTermEquiv R ι n p x) = _
      exact (monomialTermEquiv_d R ι n p x).symm)

/-- The actual sheaf complex in monomial coordinates. -/
def sheafMonomialIso (n : ℤ) : sheafComplex R ι n ≅ monomialComplex R ι n :=
  gradedIso R ι n ≪≫ monomialIso R ι n

/-- The submodule supported on one integer exponent across all tuples. -/
def exponentSummand (n : ℤ) (q : ℕ) (e : ι →₀ ℤ) :
    Submodule R (MonomialTerm R ι n q) where
  carrier := {x | ∀ a (f : AllowedExponent a n), f.val ≠ e → x a f = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro a f hf
    simp only [Pi.add_apply, Finsupp.add_apply, hx a f hf, hy a f hf, add_zero]
  smul_mem' r x hx := by
    intro a f hf
    simp only [Pi.smul_apply, Finsupp.smul_apply, hx a f hf, smul_zero]

/-- No face map mixes distinct integer exponents, including for negative twists. -/
lemma monomialDifferential_mem_summand (n : ℤ) (q : ℕ) (e : ι →₀ ℤ)
    (x : MonomialTerm R ι n q) (hx : x ∈ exponentSummand R ι n q e) :
    monomialDifferential R ι n q x ∈ exponentSummand R ι n (q + 1) e := by
  classical
  intro a f hf
  rw [monomialDifferential_apply, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finsupp.smul_apply]
  suffices Finsupp.mapDomain (exponentFace q a k n) (x (a ∘ k.succAbove)) f = 0 by
    rw [this, smul_zero]
  by_cases h : f ∈ Set.range (exponentFace q a k n)
  · obtain ⟨g, rfl⟩ := h
    rw [Finsupp.mapDomain_apply_of_injective (exponentFace q a k n).injective]
    exact hx _ g hf
  · exact Finsupp.mapDomain_of_notMem_range _ _ h

/-- Restrict the monomial differential to a single exponent for subsequent computation. -/
def exponentDifferential (n : ℤ) (q : ℕ) (e : ι →₀ ℤ) :
    exponentSummand R ι n q e →ₗ[R] exponentSummand R ι n (q + 1) e :=
  (monomialDifferential R ι n q).restrict
    (fun x hx ↦ monomialDifferential_mem_summand R ι n q e x hx)

/-- Each integer exponent defines its own Cech subcomplex. -/
def exponentComplex (n : ℤ) (e : ι →₀ ℤ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (exponentSummand R ι n q e))
    (fun q ↦ ModuleCat.ofHom (exponentDifferential R ι n q e)) (fun q ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact monomialDifferential_sq R ι n q x.val)

end FLT.Mazur.ProjectiveSpace.TwistGradedCech
