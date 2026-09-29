/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistGradedCech

/-!
# Scalar coordinates for an exponent summand

An exponent contributes on precisely the tuples containing every index at which
it is negative. Its differential is the ordinary alternating tuple differential,
with zero coefficients on the other tuples. These coordinates describe the
actual monomial summands of the twisting-sheaf Cech complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

open LocalizationDegree TwistGradedCech

variable (R : Type u) [CommRing R] (ι : Type u)
variable (n : ℤ) (e : ι →₀ ℤ)

/-- A tuple supports the exponent if its complement has no negative entry. -/
def Supported {m : ℕ} (a : Fin m → ι) : Prop :=
  e.degree = n ∧ ∀ i ∉ Set.range a, 0 ≤ e i

/-- Scalar tuple cochains supported on the tuples allowing the fixed exponent. -/
def scalarTerm (q : ℕ) : Submodule R ((Fin (q + 1) → ι) → R) where
  carrier := {x | ∀ a, ¬ Supported ι n e a → x a = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro a ha
    simp only [Pi.add_apply, hx a ha, hy a ha, add_zero]
  smul_mem' r x hx := by
    intro a ha
    simp only [Pi.smul_apply, hx a ha, smul_zero]

/-- Extend a tuple's monomial coordinates by zero to all integer exponents. -/
def extend (q : ℕ) (a : Fin (q + 1) → ι) :
    (AllowedExponent a n →₀ R) →ₗ[R] ((ι →₀ ℤ) →₀ R) :=
  Finsupp.lmapDomain R R Subtype.val

lemma extend_apply (q : ℕ) (a : Fin (q + 1) → ι)
    (x : AllowedExponent a n →₀ R) (f : AllowedExponent a n) :
    extend R ι n q a x f.val = x f :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective x f

lemma extend_eq_zero (q : ℕ) (a : Fin (q + 1) → ι)
    (x : AllowedExponent a n →₀ R) (h : ¬ Supported ι n e a) :
    extend R ι n q a x e = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨f, rfl⟩
  exact h f.property

/-- Extract the fixed exponent's coefficient on every tuple. -/
def scalarCoordinates (q : ℕ) :
    exponentSummand R ι n q e →ₗ[R] scalarTerm R ι n e q where
  toFun x := ⟨fun a ↦ extend R ι n q a (x.val a) e,
    fun a ha ↦ extend_eq_zero R ι n e q a (x.val a) ha⟩
  map_add' x y := by
    apply Subtype.ext
    funext a
    exact congrArg (fun z ↦ z e) (map_add (extend R ι n q a) _ _)
  map_smul' r x := by
    apply Subtype.ext
    funext a
    exact congrArg (fun z ↦ z e) (map_smul (extend R ι n q a) r _)

/-- Reconstruct a summand by putting a single monomial on each supported tuple. -/
def scalarReconstruct (q : ℕ) (x : scalarTerm R ι n e q) :
    exponentSummand R ι n q e := by
  classical
  refine ⟨fun a ↦ if h : Supported ι n e a then Finsupp.single ⟨e, h⟩ (x.val a) else 0,
    ?_⟩
  intro a f hf
  dsimp only
  split_ifs with h
  · exact Finsupp.single_eq_of_ne (fun he ↦ hf (congrArg Subtype.val he))
  · rfl

lemma scalarCoordinates_reconstruct (q : ℕ) (x : scalarTerm R ι n e q) :
    scalarCoordinates R ι n e q (scalarReconstruct R ι n e q x) = x := by
  classical
  apply Subtype.ext
  funext a
  change extend R ι n q a
    (if h : Supported ι n e a then Finsupp.single ⟨e, h⟩ (x.val a) else 0) e = x.val a
  split_ifs with h
  · simp [extend, Finsupp.lmapDomain_apply]
  · rw [map_zero, Finsupp.zero_apply, x.property a h]

lemma scalarReconstruct_coordinates (q : ℕ) (x : exponentSummand R ι n q e) :
    scalarReconstruct R ι n e q (scalarCoordinates R ι n e q x) = x := by
  classical
  apply Subtype.ext
  funext a
  apply Finsupp.ext
  intro f
  change (if h : Supported ι n e a then
    Finsupp.single ⟨e, h⟩ (extend R ι n q a (x.val a) e) else 0) f = x.val a f
  by_cases hf : f.val = e
  · subst e
    rw [dite_eq_left (show Supported ι n f.val a from f.property)]
    change (Finsupp.single f (extend R ι n q a (x.val a) f.val)) f = _
    rw [Finsupp.single_eq_same, extend_apply]
  · rw [x.property a f hf]
    split_ifs with h
    · exact Finsupp.single_eq_of_ne (fun he ↦ hf (congrArg Subtype.val he))
    · rfl

/-- An actual monomial summand is equivalent to its scalar tuple coordinates. -/
def scalarEquiv (q : ℕ) :
    exponentSummand R ι n q e ≃ₗ[R] scalarTerm R ι n e q where
  __ := scalarCoordinates R ι n e q
  invFun := scalarReconstruct R ι n e q
  left_inv := scalarReconstruct_coordinates R ι n e q
  right_inv := scalarCoordinates_reconstruct R ι n e q

/-- Supporting a face implies supporting the whole tuple. -/
lemma supported_of_face (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2))
    (h : Supported ι n e (a ∘ k.succAbove)) : Supported ι n e a :=
  ⟨h.1, fun i hi ↦ h.2 i (fun ⟨j, hj⟩ ↦ hi ⟨k.succAbove j, hj⟩)⟩

/-- The ordinary alternating differential restricted to supported scalar cochains. -/
def scalarDifferential (q : ℕ) :
    scalarTerm R ι n e q →ₗ[R] scalarTerm R ι n e (q + 1) where
  toFun x := ⟨fun a ↦ ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • x.val (a ∘ k.succAbove),
    by
      intro a ha
      apply Finset.sum_eq_zero
      intro k _
      rw [x.property _ (fun h ↦ ha (supported_of_face ι n e q a k h)), smul_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    funext a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    apply Subtype.ext
    funext a
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
      (r • x.val (a ∘ k.succAbove))) =
        r • ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) • x.val (a ∘ k.succAbove)
    simp only [Finset.smul_sum, smul_comm r]

lemma extend_face (q : ℕ) (a : Fin (q + 2) → ι) (k : Fin (q + 2))
    (x : AllowedExponent (a ∘ k.succAbove) n →₀ R) :
    extend R ι n (q + 1) a (Finsupp.mapDomain (exponentFace q a k n) x) =
      extend R ι n q (a ∘ k.succAbove) x := by
  change Finsupp.mapDomain Subtype.val (Finsupp.mapDomain (exponentFace q a k n) x) = _
  rw [← Finsupp.mapDomain_comp]
  rfl

/-- In scalar coordinates the B10 differential is the alternating tuple differential. -/
lemma scalarEquiv_d (q : ℕ) (x : exponentSummand R ι n q e) :
    scalarEquiv R ι n e (q + 1) (exponentDifferential R ι n q e x) =
      scalarDifferential R ι n e q (scalarEquiv R ι n e q x) := by
  apply Subtype.ext
  funext a
  change extend R ι n (q + 1) a (monomialDifferential R ι n q x.val a) e = _
  rw [monomialDifferential_apply, map_sum, Finsupp.finsetSum_apply]
  simp only [map_zsmul, Finsupp.smul_apply, extend_face]
  rfl

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
