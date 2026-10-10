/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDivisorLengthAdditivity
public import FLT.Mazur.FiniteFieldRankLength
public import FLT.Mazur.SectionSumFinite

/-!
# Length of a sum of rational sections

The image of each section is the base field and has length one. Multiplication of
Cartier ideals adds actual scheme lengths, so every finite section product has
length its number of factors. Repeated sections are counted repeatedly.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- A rational section has divisor length one. -/
theorem divisorFieldLength_section [IsSeparated f]
    (s : Spec (CommRingCat.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    divisorFieldLength f s.ker = 1 := by
  unfold divisorFieldLength
  rw [← sectionImageIso_hom f s hs]
  exact finiteSchemeLength_of_isIso _

/-- The unit ideal defines the empty finite divisor, of length zero. -/
theorem divisorFieldLength_one : divisorFieldLength f 1 = 0 := by
  let D := (1 : X.IdealSheafData).subscheme
  let q := (1 : X.IdealSheafData).subschemeι ≫ f
  let _ : IsEmpty D := isEmpty_top_subscheme
  let _ := Module.compHom Γ(D, ⊤) (structureScalarMap q)
  let _ : Subsingleton (H0 q) := (scalarH0Equiv q).injective.subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- Actual length of a section product, with multiplicity at every collision. -/
theorem divisorFieldLength_section_prod [IsProper f] [SmoothOfRelativeDimension 1 f]
    {ι : Type*} (t : Finset ι) (s : ι → (Spec (CommRingCat.of k) ⟶ X))
    (hs : ∀ i ∈ t, s i ≫ f = 𝟙 _) :
    divisorFieldLength f (∏ i ∈ t, (s i).ker) = t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.card_empty, divisorFieldLength_one]
  | @insert i t hi ih =>
    have hsi := hs i (Finset.mem_insert_self i t)
    have hst : ∀ j ∈ t, s j ≫ f = 𝟙 _ :=
      fun j hj ↦ hs j (Finset.mem_insert_of_mem hj)
    have hI := (smoothSectionCartier f (s i) inferInstance inferInstance hsi).1
    have hJ := (relativeEffectiveCartier_section_prod f t s hst).1
    let _ : IsFinite ((s i).ker.subschemeι ≫ f) := by
      rw [← sectionImageIso_hom f (s i) hsi]
      infer_instance
    let _ := isFinite_section_prod f t s hst
    let _ : IsFinite (((s i).ker * ∏ j ∈ t, (s j).ker).subschemeι ≫ f) := by
      have he := Finset.prod_insert (f := fun j ↦ (s j).ker) hi
      exact (congrArg (fun J : X.IdealSheafData ↦ IsFinite (J.subschemeι ≫ f)) he).mp
        (isFinite_section_prod f (insert i t) s hs)
    rw [Finset.prod_insert hi, divisorFieldLength_mul f hI hJ,
      divisorFieldLength_section f (s i) hsi, ih hst, Finset.card_insert_of_notMem hi]
    omega

/-- The cohomological degree of the section-sum line is the number of sections. -/
theorem section_prod_degree [IsProper f] [SmoothOfRelativeDimension 1 f]
    {ι : Type*} (t : Finset ι) (s : ι → (Spec (CommRingCat.of k) ⟶ X))
    (hs : ∀ i ∈ t, s i ≫ f = 𝟙 _) :
    curveSheafDegree f (divisorLineBundle (∏ i ∈ t, (s i).ker)
      (relativeEffectiveCartier_section_prod f t s hs).1) = (t.card : ℤ) := by
  let _ := isFinite_section_prod f t s hs
  rw [divisor_degree_eq_fieldLength, divisorFieldLength_section_prod f t s hs]

end FLT.Mazur.FCurve
