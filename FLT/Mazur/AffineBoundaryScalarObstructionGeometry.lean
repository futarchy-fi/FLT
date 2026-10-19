/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestKernels
public import FLT.Mazur.SchemeImageClosureFlatBaseChange

/-!
# Full scalar test obstruction under flat base change

The exact computed kernel product cuts out the closure of actual failed test
images. This closure commutes with flat locally finitely presented scalar
changes. The construction uses the full Cartesian product throughout.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarLocalizedIdealNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)

/-- The failed full tests, before taking an image or closing it. -/
def boundaryFailedTests : Set (boundaryProduct s κ) :=
  {z | ¬ ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal}

/-- The computed kernel product retains every limit of every actual failed test image. -/
theorem boundaryScalar_compl_failed_image :
    (boundaryScalarNilpotenceOpen s κ a : Set (PrimeSpectrum T))ᶜ =
      closure (boundaryScalarProjection s κ '' boundaryFailedTests s κ a) := by
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨Q, hQ, hf⟩ := (not_mem_scalarNilpotenceOpen_iff
      (boundaryScalarHom s κ) (boundaryTestIdeal s κ a) (boundaryTestIdeal_fg s κ a) P).mp hP
    rw [boundaryScalarHom_comap_component] at hQ
    apply ((PrimeSpectrum.le_iff_specializes _ _).mp hQ).mem_closed isClosed_closure
    apply subset_closure
    refine ⟨boundaryComponentPoint s κ Q, ?_, rfl⟩
    intro ht
    apply hf
    have hi := (boundaryTestIdeal_le_point_iff s κ a _).mpr ht
    have he : (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) =
        (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum Γ(boundaryProduct s κ, ⊤)) :=
      congrArg (fun f ↦ f (⟨Q.val, Q.property.1.1⟩ :
        PrimeSpectrum Γ(boundaryProduct s κ, ⊤))) (boundaryProduct s κ).isoSpec.inv_hom_id
    simpa only [he] using hi
  · apply closure_minimal
    · rintro _ ⟨z, hz, rfl⟩ hp
      apply hz
      apply (boundaryTestIdeal_le_point_iff s κ a z).mp
      exact FiniteIdealLocalizationDenominators.nilpotenceOpen_subset_zeroLocus _
        (boundaryScalarNilpotenceOpen_preimage s κ a hp)
    · exact (boundaryScalarNilpotenceOpen s κ a).isOpen.isClosed_compl

variable {Y : Scheme} (g : Y ⟶ Spec (.of T)) [Flat g] [LocallyOfFinitePresentation g]
local notation "π" => boundaryScalarProjection s κ
local notation "K" => boundaryFailedTests s κ a

/-- A flat scalar branch computes exactly the original closed obstruction above it. -/
theorem boundaryFailedTests_flat_closure :
    closure (pullback.snd π g '' (pullback.fst π g ⁻¹' K)) =
      g ⁻¹' PrimeSpectrum.zeroLocus (boundaryTestKernelProduct s κ a : Set T) := by
  rw [SchemeImageClosure.flat_pullback_image_closure,
    ← boundaryScalar_compl_failed_image, boundaryScalar_compl_testKernelProduct]

/-- A neighborhood on one actual flat scalar branch yields original kernel avoidance. -/
theorem boundaryScalar_mem_of_flat_neighborhood (V : Y.Opens) (y : Y) (hy : y ∈ V)
    (hV : ∀ z : (pullback π g : Scheme), pullback.snd π g z ∈ V →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ (pullback.fst π g z)).asIdeal) :
    g y ∈ boundaryScalarNilpotenceOpen s κ a := by
  have hn := SchemeImageClosure.not_mem_closure_of_flat_neighborhood π g K V y hy
    (fun z hz hbad ↦ hbad (hV z hz))
  rw [← boundaryScalar_compl_failed_image] at hn
  exact not_not.mp hn

end FLT.Mazur.AffineScalarBoundaryNilpotence
