/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpectrumTranslationNormBasis
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite-free translation refinements over principal coefficient spectra

Localize the ground ring where the original translation algebra has a finite
basis. The tensor spectrum is an actual Cartesian translation refinement;
its basis is transported to its original structural section algebra.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.EtaleTranslationBranch
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (V : Over (Spec (.of R))) [IsAffine V.left]
/-- Keep the original structural algebra when forming the localized tensor. -/
local instance refinementSectionAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom

/-- The localized coefficient spectrum. -/
def normBase (r : R) : Scheme := Spec (.of (Localization.Away r))

/-- Its original ground-base map. -/
def normBaseMap (r : R) : normBase r ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))

/-- The complete translation after this coefficient localization. -/
def normSource (r : R) : Scheme :=
  let _ := affineBaseSectionAlgebra V.hom
  Spec (.of (Localization.Away r ⊗[R] Γ(V.left, ⊤)))

/-- The structural map of the complete localized translation. -/
def normSourceBase (r : R) : normSource V r ⟶ normBase r :=
  Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away r)
    (Localization.Away r ⊗[R] Γ(V.left, ⊤))))

/-- The refinement retains the original translation, not a selected residue branch. -/
def normSourceMap (r : R) : normSource V r ⟶ V.left :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : Γ(V.left, ⊤) →ₐ[R] _).toRingHom) ≫ V.left.isoSpec.inv

instance normSource_affine (r : R) : IsAffine (normSource V r) :=
  inferInstanceAs (IsAffine (Spec _))

instance normBaseMap_open (r : R) : IsOpenImmersion (normBaseMap r) :=
  inferInstanceAs (IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))

/-- The localized translation is the full scheme base change, including every residue branch. -/
theorem normSource_isPullback (r : R) :
    IsPullback (normSourceBase V r) (normSourceMap V r) (normBaseMap r) V.hom := by
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) Γ(V.left, ⊤))
  apply H.of_iso (Iso.refl _) (Iso.refl _) V.left.isoSpec.symm (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]; rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    have h : V.left.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤))) = V.hom :=
      affineBaseSectionsSpecIso_over R V
    rw [← h, Iso.inv_hom_id_assoc]

instance normSourceMap_open (r : R) : IsOpenImmersion (normSourceMap V r) :=
  MorphismProperty.of_isPullback (normSource_isPullback V r) inferInstance

instance normSourceBase_finite [IsFinite V.hom] (r : R) : IsFinite (normSourceBase V r) :=
  MorphismProperty.of_isPullback (normSource_isPullback V r).flip inferInstance

instance normSourceBase_etale [Etale V.hom] (r : R) : Etale (normSourceBase V r) :=
  MorphismProperty.of_isPullback (normSource_isPullback V r).flip inferInstance

instance normSourceBase_surjective [Surjective V.hom] (r : R) :
    Surjective (normSourceBase V r) :=
  MorphismProperty.of_isPullback (normSource_isPullback V r).flip inferInstance

/-- A point whose ground coordinate avoids the localizing coefficient is retained. -/
theorem normSource_exists_preimage (r : R) (v : V.left) (hr : r ∉ (V.hom v).asIdeal) :
    ∃ w : normSource V r, normSourceMap V r w = v := by
  have hp : V.hom v ∈ Set.range (normBaseMap r) := by
    change V.hom v ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨p, hp⟩ := hp
  obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
    (normSource_isPullback V r) p v hp
  exact ⟨w, hw⟩

/-- Construct a localized translation with a basis on its actual sections and a retained point. -/
theorem exists_normSource_basis [Algebra.FiniteType ℤ R] [Etale V.hom] [IsFinite V.hom]
    (v : V.left) :
    ∃ r : R, r ∉ (V.hom v).asIdeal ∧ ∃ n : ℕ,
      (let _ := affineBaseSectionAlgebra (normSourceBase V r)
       Nonempty (Basis (Fin n) (Localization.Away r) Γ(normSource V r, ⊤))) ∧
      ∃ w : normSource V r, normSourceMap V r w = v := by
  obtain ⟨r, hr, n, ⟨b⟩⟩ := exists_section_principal_basis V.hom (V.hom v)
  refine ⟨r, hr, n, ?_, normSource_exists_preimage V r v hr⟩
  exact ⟨spectrumSectionBasis _ _ b⟩

end FLT.Mazur.EtaleTranslationBranch
