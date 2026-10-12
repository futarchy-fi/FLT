/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientGluedBase

/-!
# Principal chart refinements for arbitrary morphisms to the ambient Grassmannian

Pulling back the actual open charts and refining by coefficient basic opens
constructs a principal cover of every affine test. No original quotient is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)

/-- All coefficient basic opens whose images lie in one of the actual ambient chart opens. -/
def AmbientMorphismCoverIndex :=
  Σ i : AmbientChartIndex R M κ d,
    {r : A // PrimeSpectrum.basicOpen r ≤
      f ⁻¹ᵁ (ambientGrassmannianChart R M κ d i).opensRange}

/-- The local composite's entire image lies in the specified ambient chart. -/
theorem ambientMorphismCover_range (q : AmbientMorphismCoverIndex f) :
    Set.range (Spec.algebraMap A (Localization.Away q.2.val) ≫ f) ⊆
      Set.range (ambientGrassmannianChart R M κ d q.1) := by
  rintro _ ⟨z, rfl⟩
  apply q.2.property
  rw [← Scheme.Hom.opensRange_localizationAway (R := .of A) q.2.val]
  exact ⟨z, rfl⟩

/-- The actual lift of a principal-local test morphism into its ambient chart. -/
def ambientMorphismChartLift (q : AmbientMorphismCoverIndex f) :
    Spec (.of (Localization.Away q.2.val)) ⟶ splitChartScheme R κ d :=
  IsOpenImmersion.lift (ambientGrassmannianChart R M κ d q.1)
    (Spec.algebraMap A (Localization.Away q.2.val) ≫ f) (ambientMorphismCover_range f q)

/-- The chart lift retains the original test morphism after inclusion in the glued scheme. -/
@[reassoc] theorem ambientMorphismChartLift_fac (q : AmbientMorphismCoverIndex f) :
    ambientMorphismChartLift f q ≫ ambientGrassmannianChart R M κ d q.1 =
      Spec.algebraMap A (Localization.Away q.2.val) ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- Every coefficient prime lies in one of the constructed chart refinements. -/
theorem ambientMorphismCover_exists (p : PrimeSpectrum A) :
    ∃ q : AmbientMorphismCoverIndex f, p ∈ PrimeSpectrum.basicOpen q.2.val := by
  obtain ⟨i, y, hy⟩ := ambientGrassmannianChart_cover R M κ d (f p)
  have hp : p ∈ f ⁻¹ᵁ (ambientGrassmannianChart R M κ d i).opensRange := ⟨y, hy⟩
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp
      (f ⁻¹ᵁ (ambientGrassmannianChart R M κ d i).opensRange).isOpen
  exact ⟨⟨i, ⟨r, hle⟩⟩, hr⟩

/-- An actual coefficient principal open cover of every affine scheme test. -/
def ambientMorphismPrincipalCover : (Spec (.of A)).OpenCover where
  I₀ := AmbientMorphismCoverIndex f
  X q := Spec (.of (Localization.Away q.2.val))
  f q := Spec.algebraMap A (Localization.Away q.2.val)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, fun q ↦ inferInstance⟩
    obtain ⟨q, hq⟩ := ambientMorphismCover_exists f p
    refine ⟨q, (basicOpenIsoSpecAway (R := .of A) q.2.val).hom ⟨p, hq⟩, ?_⟩
    exact congrArg (fun g ↦ g ⟨p, hq⟩)
      (basicOpenIsoSpecAway_hom_SpecMap (R := .of A) q.2.val)

/-- The coefficients of the pulled-back chart refinements generate the unit ideal. -/
theorem ambientMorphismCover_span :
    Ideal.span (Set.range (fun q : AmbientMorphismCoverIndex f ↦ q.2.val)) = ⊤ := by
  by_contra h
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
  let _ := hp.isPrime
  obtain ⟨q, hq⟩ := ambientMorphismCover_exists f ⟨p, inferInstance⟩
  exact hq (hle (Ideal.subset_span ⟨q, rfl⟩))

end FLT.Mazur.GrassmannianChart
