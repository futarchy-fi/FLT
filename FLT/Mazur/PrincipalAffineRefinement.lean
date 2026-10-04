/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.Tactic.IrreducibleDef

/-!
# Principal refinements of an affine chart

An affine chart can be shrunk around a specified point to lie inside any
specified open neighborhood. The refined chart is the spectrum of an actual
localization, and its image has precisely that ring of regular functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.PrincipalAffineRefinement
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The localization inclusion defining a principal refinement. -/
def inclusion (f : R) : Spec (.of (Localization.Away f)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))

instance inclusion_isOpenImmersion (f : R) : IsOpenImmersion (inclusion f) :=
  IsOpenImmersion.of_isLocalization f

/-- The image is exactly the specified basic open. -/
lemma range_inclusion (f : R) : Set.range (inclusion f) =
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away f) f

/-- The prime-spectrum basis provides an actual denominator around the point. -/
lemma exists_denominator (j : Spec (.of R) ⟶ X) (U : X.Opens)
    (x : Spec (.of R)) (hx : j x ∈ U) :
    ∃ f : R, x ∈ PrimeSpectrum.basicOpen f ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ j ⁻¹' U := by
  obtain ⟨V, ⟨f, rfl⟩, hf, hV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      hx (U.isOpen.preimage j.continuous)
  exact ⟨f, hf, hV⟩

/-- Composing the actual localization inclusion with the affine chart. -/
def chart (j : Spec (.of R) ⟶ X) (f : R) : Spec (.of (Localization.Away f)) ⟶ X :=
  inclusion f ≫ j

instance chart_isOpenImmersion (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] (f : R) :
    IsOpenImmersion (chart j f) := by
  unfold chart
  infer_instance

/-- No extra points appear in the image of the localization chart. -/
lemma range_chart (j : Spec (.of R) ⟶ X) (f : R) :
    Set.range (chart j f) = j '' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  rw [← range_inclusion]
  exact Set.range_comp j (inclusion f)

/-- The refined chart contains the chosen point. -/
lemma mem_range_chart (j : Spec (.of R) ⟶ X) (f : R) (x : Spec (.of R))
    (hx : x ∈ PrimeSpectrum.basicOpen f) : j x ∈ Set.range (chart j f) := by
  rw [range_chart]
  exact ⟨x, hx, rfl⟩

/-- The entire refined image lies in the required open. -/
lemma range_chart_subset (j : Spec (.of R) ⟶ X) (f : R) (U : X.Opens)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ j ⁻¹' U) :
    Set.range (chart j f) ⊆ U := by
  rw [range_chart]
  rintro _ ⟨x, hx, rfl⟩
  exact hf hx

/-- The section ring of the image is the actual localization ring. -/
def sectionsIso (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] (f : R) :
    Γ(X, chart j f ''ᵁ ⊤) ≅ CommRingCat.of (Localization.Away f) :=
  (chart j f).appIso ⊤ ≪≫ Scheme.ΓSpecIso (.of (Localization.Away f))

/-- A denominator selected from the actual basic-open basis. -/
irreducible_def denominator (j : Spec (.of R) ⟶ X) (U : X.Opens)
    (x : Spec (.of R)) (hx : j x ∈ U) : R :=
  Classical.choose (exists_denominator j U x hx)

/-- The selected denominator does not vanish at the chosen point. -/
lemma mem_denominator (j : Spec (.of R) ⟶ X) (U : X.Opens)
    (x : Spec (.of R)) (hx : j x ∈ U) :
    x ∈ PrimeSpectrum.basicOpen (denominator j U x hx) := by
  rw [denominator_def]
  exact (Classical.choose_spec (exists_denominator j U x hx)).1

/-- The selected principal open avoids the complement of the specified open. -/
lemma denominator_subset (j : Spec (.of R) ⟶ X) (U : X.Opens)
    (x : Spec (.of R)) (hx : j x ∈ U) :
    (PrimeSpectrum.basicOpen (denominator j U x hx) : Set (PrimeSpectrum R)) ⊆ j ⁻¹' U := by
  rw [denominator_def]
  exact (Classical.choose_spec (exists_denominator j U x hx)).2

end FLT.Mazur.PrincipalAffineRefinement
