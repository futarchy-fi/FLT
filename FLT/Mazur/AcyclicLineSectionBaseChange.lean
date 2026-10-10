/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CohomologicallyFlatSections
public import FLT.Mazur.FlatLineSectionTerms
public import FLT.Mazur.IdealPowerExtensionCharts

/-!
# Universal section base change for cohomologically flat lines

A finite affine cover is constructed from the Noetherian source. Flatness of
the family gives flat terms without any coefficient-complex hypothesis.
Vanishing of positive cohomology suffices, and the new base need not be flat.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherian X] [X.IsSeparated]
  (f : X ⟶ S) [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hH : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)))

include hL hH in
/-- Flat positive cohomology forces the actual line-section module to be base-flat. -/
theorem sections_flat : Module.Flat Γ(S, ⊤) (baseSections L f.appTop.hom ⊤) := by
  let _ := hL.isFinitePresentation
  obtain ⟨ι, hι, U, hU⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ : Finite ι := hι
  let _ := Fintype.ofFinite ι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) n
  exact sections_flat_of_positive_ringH L (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU hH

/-- A cohomologically flat line commutes with every affine change of base. -/
def sectionsEquiv {P T : Scheme.{0}} [IsAffine T]
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections L f.appTop.hom ⊤ ≃ₗ[Γ(T, ⊤)]
      baseSections ((pullback p).obj L) q.appTop.hom ⊤ := by
  let _ := hL.isFinitePresentation
  let ι := (IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)).choose
  let hι := (IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)).choose_spec
  let _ : Finite ι := hι.choose
  let U := hι.choose_spec.choose
  have hU : iSup (fun i ↦ (U i).1) = ⊤ := hι.choose_spec.choose_spec
  let _ := Fintype.ofFinite ι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) n
  exact cohomologicallyFlatSectionsEquiv h L
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU hH

variable (hV : ∀ n, Subsingleton (ModuleH L (n + 1)))

omit [IsAffine S] [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated] [Flat f] in
include hV in
/-- Vanishing actual positive cohomology supplies all cohomological flatness hypotheses. -/
theorem positive_flat_of_vanishing (n : ℕ) :
    Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)) := by
  let _ : Subsingleton (ModuleRingH f.appTop.hom L (n + 1)) := hV n
  infer_instance

include hL hV in
/-- A positive-acyclic line has a flat module of actual sections. -/
theorem acyclic_sections_flat : Module.Flat Γ(S, ⊤) (baseSections L f.appTop.hom ⊤) :=
  sections_flat f L hL (positive_flat_of_vanishing f L hV)

/-- Positive acyclicity gives universal affine base change for actual line sections. -/
def acyclicSectionsEquiv {P T : Scheme.{0}} [IsAffine T]
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections L f.appTop.hom ⊤ ≃ₗ[Γ(T, ⊤)]
      baseSections ((pullback p).obj L) q.appTop.hom ⊤ :=
  sectionsEquiv f L hL (positive_flat_of_vanishing f L hV) h

end FLT.Mazur.LineSectionBaseChange
