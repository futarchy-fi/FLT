/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyCoordinates
public import Mathlib.Algebra.DirectSum.Module

/-!
# Direct-sum coordinates for the twisting-sheaf Cech complex

For finitely many charts, the union of the coefficient supports over all tuples
in a fixed degree is finite. This gives a direct sum of the actual exponent
subcomplexes, compatible with the original sheaf comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped DirectSum

universe u

namespace FLT.Mazur.ProjectiveSpace.TwistCechCohomology

open LocalizationDegree TwistGradedCech

variable (R : Type u) [CommRing R] (ι : Type u) (n : ℤ)

/-- Integer exponents of the specified total degree. -/
abbrev DegreeExponent := {e : ι →₀ ℤ // e.degree = n}

/-- Classical equality for indexing the direct sum. -/
local instance degreeExponentDecidableEq : DecidableEq (DegreeExponent ι n) :=
  Classical.decEq _

/-- Classical equality for filtering integer exponents. -/
local instance exponentValueDecidableEq : DecidableEq (ι →₀ ℤ) := Classical.decEq _

/-- The direct sum of the actual exponent submodules in one cochain degree. -/
abbrev SumTerm (q : ℕ) :=
  ⨁ e : DegreeExponent ι n, exponentSummand R ι n q e.val

/-- Projection to one exponent, retaining the original monomial coordinates. -/
def exponentProjection (q : ℕ) (e : DegreeExponent ι n) :
    MonomialTerm R ι n q →ₗ[R] exponentSummand R ι n q e.val := by
  classical
  refine
    { toFun := fun x ↦ ⟨fun a ↦ (x a).filter (fun f ↦ f.val = e.val), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro a f hf
    exact Finsupp.filter_apply_neg _ _ hf
  · intro x y
    apply Subtype.ext
    funext a
    ext f
    simp only [Finsupp.filter_apply, Pi.add_apply, Finsupp.add_apply]
    split_ifs <;> simp_all
  · intro r x
    apply Subtype.ext
    funext a
    ext f
    simp only [Finsupp.filter_apply, Pi.smul_apply, Finsupp.smul_apply,
      RingHom.id_apply]
    split_ifs <;> simp_all

lemma exponentProjection_apply (q : ℕ) (e : DegreeExponent ι n)
    (x : MonomialTerm R ι n q) (a : Fin (q + 1) → ι) (f : AllowedExponent a n) :
    (exponentProjection R ι n q e x).val a f =
      if f.val = e.val then x a f else 0 := rfl

variable [Fintype ι]

/-- A finite union, over the finitely many tuples, bounds all occurring exponents. -/
def exponentSupport (q : ℕ) (x : MonomialTerm R ι n q) : Finset (DegreeExponent ι n) := by
  classical
  exact Finset.univ.biUnion fun a ↦ (x a).support.image fun f ↦ ⟨f.val, f.property.1⟩

lemma exponentProjection_eq_zero (q : ℕ) (x : MonomialTerm R ι n q)
    (e : DegreeExponent ι n) (he : e ∉ exponentSupport R ι n q x) :
    exponentProjection R ι n q e x = 0 := by
  classical
  apply Subtype.ext
  funext a
  ext f
  rw [exponentProjection_apply]
  split_ifs with hf
  · by_contra hx
    apply he
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
    exact ⟨f, Finsupp.mem_support_iff.mpr hx, Subtype.ext hf⟩
  · rfl

/-- Coefficient extraction has finite support because the set of tuples is finite. -/
def sumCoordinates (q : ℕ) : MonomialTerm R ι n q →ₗ[R] SumTerm R ι n q := by
  classical
  refine
    { toFun := fun x ↦ ⟨fun e ↦ exponentProjection R ι n q e x,
        Trunc.mk ⟨(exponentSupport R ι n q x).val, ?_⟩⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro e
    by_cases he : e ∈ exponentSupport R ι n q x
    · exact Or.inl he
    · exact Or.inr (exponentProjection_eq_zero R ι n q x e he)
  · intro x y
    apply DFinsupp.ext
    intro e
    exact map_add (exponentProjection R ι n q e) x y
  · intro r x
    apply DFinsupp.ext
    intro e
    exact map_smul (exponentProjection R ι n q e) r x

lemma sumCoordinates_apply (q : ℕ) (x : MonomialTerm R ι n q)
    (e : DegreeExponent ι n) :
    sumCoordinates R ι n q x e = exponentProjection R ι n q e x := rfl

/-- Sum the inclusions of the exponent submodules. -/
def sumReconstruct (q : ℕ) : SumTerm R ι n q →ₗ[R] MonomialTerm R ι n q :=
  DirectSum.toModule R _ _ fun e ↦ (exponentSummand R ι n q e.val).subtype

omit [Fintype ι] in
lemma sumReconstruct_lof (q : ℕ) (e : DegreeExponent ι n)
    (x : exponentSummand R ι n q e.val) :
    sumReconstruct R ι n q (DirectSum.lof R _ _ e x) = x.val :=
  DirectSum.toModule_lof R
    (φ := fun e : DegreeExponent ι n ↦ (exponentSummand R ι n q e.val).subtype) e x

omit [Fintype ι] in
/-- Each coefficient of a reconstructed cochain comes from just one summand. -/
lemma sumReconstruct_apply (q : ℕ) (x : SumTerm R ι n q)
    (a : Fin (q + 1) → ι) (f : AllowedExponent a n) :
    sumReconstruct R ι n q x a f = (x ⟨f.val, f.property.1⟩).val a f := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | of e x =>
    rw [← DirectSum.lof_eq_of R, sumReconstruct_lof]
    by_cases he : e = ⟨f.val, f.property.1⟩
    · subst e
      rw [DirectSum.lof_apply]
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
      exact x.property a f (fun h ↦ he (Subtype.ext h.symm))

lemma sumReconstruct_coordinates (q : ℕ) (x : MonomialTerm R ι n q) :
    sumReconstruct R ι n q (sumCoordinates R ι n q x) = x := by
  classical
  funext a
  ext f
  rw [sumReconstruct_apply, sumCoordinates_apply, exponentProjection_apply, ite_eq_left rfl]

lemma sumCoordinates_reconstruct (q : ℕ) (x : SumTerm R ι n q) :
    sumCoordinates R ι n q (sumReconstruct R ι n q x) = x := by
  classical
  apply DFinsupp.ext
  intro e
  apply Subtype.ext
  funext a
  ext f
  rw [sumCoordinates_apply, exponentProjection_apply, sumReconstruct_apply]
  by_cases hf : f.val = e.val
  · rw [ite_eq_left hf]
    have he : (⟨f.val, f.property.1⟩ : DegreeExponent ι n) = e := Subtype.ext hf
    rw [he]
  · rw [ite_eq_right hf, (x e).property a f hf]

/-- The finite-support coordinates and summation are inverse linear maps. -/
def sumTermEquiv (q : ℕ) : MonomialTerm R ι n q ≃ₗ[R] SumTerm R ι n q where
  __ := sumCoordinates R ι n q
  invFun := sumReconstruct R ι n q
  left_inv := sumReconstruct_coordinates R ι n q
  right_inv := sumCoordinates_reconstruct R ι n q

/-- The differential on the direct sum is the componentwise exponent differential. -/
def sumDifferential (q : ℕ) : SumTerm R ι n q →ₗ[R] SumTerm R ι n (q + 1) :=
  DirectSum.lmap fun e ↦ exponentDifferential R ι n q e.val

omit [Fintype ι] in
lemma sumReconstruct_d (q : ℕ) (x : SumTerm R ι n q) :
    sumReconstruct R ι n (q + 1) (sumDifferential R ι n q x) =
      monomialDifferential R ι n q (sumReconstruct R ι n q x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | of e x =>
    rw [← DirectSum.lof_eq_of R]
    simp only [sumDifferential, DirectSum.lmap_lof, sumReconstruct_lof]
    rfl

/-- The coordinates intertwine the actual monomial differential with the direct sum. -/
lemma sumTermEquiv_d (q : ℕ) (x : MonomialTerm R ι n q) :
    sumTermEquiv R ι n (q + 1) (monomialDifferential R ι n q x) =
      sumDifferential R ι n q (sumTermEquiv R ι n q x) := by
  apply (sumTermEquiv R ι n (q + 1)).symm.injective
  change sumReconstruct R ι n (q + 1) (sumCoordinates R ι n (q + 1) _) = _
  change sumReconstruct R ι n (q + 1) (sumCoordinates R ι n (q + 1) _) =
    sumReconstruct R ι n (q + 1) (sumDifferential R ι n q (sumCoordinates R ι n q x))
  rw [sumReconstruct_coordinates, sumReconstruct_d, sumReconstruct_coordinates]

omit [Fintype ι] in
lemma sumDifferential_sq (q : ℕ) (x : SumTerm R ι n q) :
    sumDifferential R ι n (q + 1) (sumDifferential R ι n q x) = 0 := by
  apply DFinsupp.ext
  intro e
  apply Subtype.ext
  exact monomialDifferential_sq R ι n q (x e).val

/-- The direct sum of the exponent complexes, with its componentwise differential. -/
def sumComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (SumTerm R ι n q))
    (fun q ↦ ModuleCat.ofHom (sumDifferential R ι n q)) (fun q ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact sumDifferential_sq R ι n q)

/-- The monomial complex is the direct sum of its exponent subcomplexes. -/
def sumIso : monomialComplex R ι n ≅ sumComplex R ι n :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (sumTermEquiv R ι n q).toModuleIso)
    (fun p q h ↦ by
      obtain rfl : p + 1 = q := h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp only [monomialComplex, sumComplex, CochainComplex.of_d]
      exact (sumTermEquiv_d R ι n p x).symm)

/-- The original sheaf comparison followed by the finite-support decomposition. -/
def sheafSumIso : sheafComplex R ι n ≅ sumComplex R ι n :=
  sheafMonomialIso R ι n ≪≫ sumIso R ι n

lemma sheafSumIso_hom_apply (q : ℕ) (x : (TwistCech.complex R ι n).X q)
    (e : DegreeExponent ι n) :
    DFinsupp.toFun ((sheafSumIso R ι n).hom.f q x : SumTerm R ι n q) e =
      exponentProjection R ι n q e (sheafMonomialEquiv R ι n q x) := rfl

end FLT.Mazur.ProjectiveSpace.TwistCechCohomology
