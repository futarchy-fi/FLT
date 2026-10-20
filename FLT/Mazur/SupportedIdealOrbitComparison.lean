/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SupportedIdealPowerComparison
public import FLT.Mazur.SectionSumFinite

/-!
# Extending a full orbit ideal from an open subscheme

An equality with a product of closed section kernels on a containing open
extends to the ambient curve, with repeated sections and multiplicities intact.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OpenIdealCover

universe u
variable {X Y Z : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

omit [IsOpenImmersion j] in
/-- A product of closed maps through an open has support in that open. -/
theorem ker_comp_prod_support {ι : Type*} (s : Finset ι) (i : ι → (Z ⟶ X))
    [∀ a, IsClosedImmersion (i a ≫ j)] :
    Set.range (∏ a ∈ s, (i a ≫ j).ker).subschemeι ⊆ Set.range j := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  intro y hy
  obtain ⟨a, _, ha⟩ := (FCurve.mem_support_prod s (fun a ↦ (i a ≫ j).ker) y).mp hy
  change y ∈ ((i a ≫ j).ker.support : Set Y) at ha
  rw [Scheme.Hom.support_ker,
    (i a ≫ j).isClosedEmbedding.isClosed_range.closure_eq] at ha
  obtain ⟨z, rfl⟩ := ha
  exact ⟨i a z, rfl⟩

/-- The entire ambient ideal is the orbit product computed on the containing open. -/
theorem eq_ker_comp_prod {ι : Type*} (I : Y.IdealSheafData)
    (hI : Set.range I.subschemeι ⊆ Set.range j) (s : Finset ι) (i : ι → (Z ⟶ X))
    [∀ a, IsClosedImmersion (i a ≫ j)]
    (h : I.comap j = ∏ a ∈ s, (i a).ker) : I = ∏ a ∈ s, (i a ≫ j).ker := by
  apply eq_of_supported_comap_eq j I _ hI (ker_comp_prod_support j s i)
  rw [FCurve.idealSheaf_comap_prod]
  simpa only [ker_comp_comap] using h

end FLT.Mazur.OpenIdealCover
