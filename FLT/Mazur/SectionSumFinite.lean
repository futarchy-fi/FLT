/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RelativeSums
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finiteness of sums of sections

Each fiber of the closed subscheme defined by a finite product of section
ideals is supported on the finitely many values of those sections. For a
proper ambient family, properness and these finite fibers give a finite
morphism. Sections in a smooth open also give flatness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}}

/-- The support of a finite ideal product is the union of the individual supports. -/
lemma mem_support_prod {ι : Type*} (t : Finset ι) (I : ι → X.IdealSheafData) (x : X) :
    x ∈ (∏ i ∈ t, I i).support ↔ ∃ i ∈ t, x ∈ (I i).support := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [← SetLike.mem_coe]
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul]
    change (x ∈ (I i).support ∨ x ∈ (∏ j ∈ t, I j).support) ↔ _
    rw [ih]
    simp only [Finset.mem_insert]
    aesop

/-- A section sum has finite set-theoretic fibers, including repeated or empty sections. -/
theorem finite_fibers_section_prod {ι : Type*} (f : X ⟶ S) [IsSeparated f]
    (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i ∈ t, s i ≫ f = 𝟙 S) (y : S) :
    (((∏ i ∈ t, (s i).ker).subschemeι ≫ f) ⁻¹' {y}).Finite := by
  let I : X.IdealSheafData := ∏ i ∈ t, (s i).ker
  have hfin : ((fun i ↦ s i y) '' (t : Set ι)).Finite :=
    t.finite_toSet.image _
  apply (Set.Finite.preimage I.subschemeι.injective.injOn hfin).subset
  intro x hx
  have hsupport : I.subschemeι x ∈ I.support := by
    rw [← SetLike.mem_coe, ← I.range_subschemeι]
    exact ⟨x, rfl⟩
  obtain ⟨i, hi, himem⟩ := (mem_support_prod t (fun i ↦ (s i).ker) _).mp hsupport
  rw [← SetLike.mem_coe, support_section_ker f (s i) (hs i hi)] at himem
  obtain ⟨z, hz⟩ := himem
  have hzy : z = y := by
    calc
      z = f (s i z) := by
        simpa using (congrArg (fun g : S ⟶ S ↦ g z) (hs i hi)).symm
      _ = f (I.subschemeι x) := congrArg f hz
      _ = y := hx
  exact ⟨i, hi, by simpa only [hzy] using hz⟩

/-- A finite sum of sections of a proper family is finite over its base. -/
theorem isFinite_section_prod {ι : Type*} (f : X ⟶ S) [IsProper f]
    (t : Finset ι) (s : ι → (S ⟶ X)) (hs : ∀ i ∈ t, s i ≫ f = 𝟙 S) :
    IsFinite ((∏ i ∈ t, (s i).ker).subschemeι ≫ f) := by
  let : LocallyQuasiFinite ((∏ i ∈ t, (s i).ker).subschemeι ≫ f) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _
      (finite_fibers_section_prod f t s hs)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Smooth-open section sums in a proper family are finite and flat over the base. -/
theorem finite_flat_smoothOpen_section_prod {U : Scheme.{u}} {ι : Type*}
    (j : U ⟶ X) (f : X ⟶ S) [IsOpenImmersion j] [IsProper f]
    [SmoothOfRelativeDimension 1 (j ≫ f)]
    (t : Finset ι) (s : ι → (S ⟶ U)) (hs : ∀ i ∈ t, s i ≫ j ≫ f = 𝟙 S) :
    IsFinite ((∏ i ∈ t, (s i ≫ j).ker).subschemeι ≫ f) ∧
      Flat ((∏ i ∈ t, (s i ≫ j).ker).subschemeι ≫ f) :=
  ⟨isFinite_section_prod f t (fun i ↦ s i ≫ j)
      (fun i hi ↦ by simpa only [Category.assoc] using hs i hi),
    (relativeEffectiveCartier_smoothOpen_section_prod j f t s hs).2⟩

end FLT.Mazur.FCurve
