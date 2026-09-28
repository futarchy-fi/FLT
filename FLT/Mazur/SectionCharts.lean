/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Compatible affine charts for a smooth section

A standard smooth chart can be shrunk simultaneously on the base and source so
that the section lands in it. The resulting coordinate maps are the restrictions
of the original scheme morphisms and give an augmented algebra of relative dimension one.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X)

/-- An affine standard smooth chart through a section, with both landing conditions. -/
structure SectionChart (y : S) where
  /-- The affine neighborhood of the base point. -/
  base : S.affineOpens
  /-- The affine neighborhood of the section point. -/
  source : X.affineOpens
  /-- The base point is in the chart. -/
  mem_base : y ∈ base.1
  /-- The structure map lands in the base chart. -/
  source_le : source.1 ≤ f ⁻¹ᵁ base.1
  /-- The section lands in the source chart. -/
  base_le : base.1 ≤ s ⁻¹ᵁ source.1
  /-- The actual map on coordinate rings is standard smooth of dimension one. -/
  standardSmooth : RingHom.IsStandardSmoothOfRelativeDimension 1
    (f.appLE base source source_le).hom

namespace SectionChart

variable {f s} {y : S} (C : SectionChart f s y)

/-- The source chart contains the section point. -/
lemma mem_source : s y ∈ C.source.1 := C.base_le C.mem_base

/-- The restricted structure morphism. -/
def structureMap : C.source.1.toScheme ⟶ C.base.1.toScheme :=
  f.resLE C.base C.source C.source_le

/-- The restricted section. -/
def sectionMap : C.base.1.toScheme ⟶ C.source.1.toScheme :=
  s.resLE C.source C.base C.base_le

@[reassoc (attr := simp)]
lemma structureMap_ι : C.structureMap ≫ C.base.1.ι = C.source.1.ι ≫ f :=
  f.resLE_comp_ι C.source_le

@[reassoc (attr := simp)]
lemma sectionMap_ι : C.sectionMap ≫ C.source.1.ι = C.base.1.ι ≫ s :=
  s.resLE_comp_ι C.base_le

/-- Restriction preserves the section identity. -/
@[simp]
lemma sectionMap_structureMap (hs : s ≫ f = 𝟙 S) :
    C.sectionMap ≫ C.structureMap = 𝟙 C.base.1.toScheme := by
  apply (cancel_mono C.base.1.ι).mp
  simp [hs]

/-- The structure homomorphism on the actual coordinate rings. -/
def ringMap : Γ(S, C.base) →+* Γ(X, C.source) :=
  (f.appLE C.base C.source C.source_le).hom

/-- The augmentation is the actual restriction of the section. -/
def augmentation : Γ(X, C.source) →+* Γ(S, C.base) :=
  (s.appLE C.source C.base C.base_le).hom

/-- The coordinate maps retain the section identity. -/
lemma augmentation_comp_ringMap (hs : s ≫ f = 𝟙 S) :
    C.augmentation.comp C.ringMap = RingHom.id _ := by
  change (f.appLE C.base C.source C.source_le ≫
    s.appLE C.source C.base C.base_le).hom = _
  rw [Scheme.Hom.appLE_comp_appLE]
  simp only [hs]
  change (𝟙 Γ(S, C.base) ≫ S.presheaf.map (𝟙 (Opposite.op C.base.1))).hom = _
  simp

/-- The algebra structure on the source coordinate ring comes from `f.appLE`. -/
abbrev algebra : Algebra Γ(S, C.base) Γ(X, C.source) := C.ringMap.toAlgebra

/-- The section induces an augmentation over the base coordinate ring. -/
def augmentationAlgHom (hs : s ≫ f = 𝟙 S) :
    letI := C.algebra
    Γ(X, C.source) →ₐ[Γ(S, C.base)] Γ(S, C.base) := by
  letI := C.algebra
  exact { C.augmentation with
    commutes' := fun r ↦ congrArg (fun g : Γ(S, C.base) →+* Γ(S, C.base) ↦ g r)
      (C.augmentation_comp_ringMap hs) }

/-- Standard smoothness for the algebra structure used by the augmentation. -/
lemma algebra_standardSmooth :
    letI := C.algebra
    Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(S, C.base) Γ(X, C.source) :=
  C.standardSmooth

/-- The prime at the section point, in the source coordinate ring. -/
def sectionPrime : PrimeSpectrum Γ(X, C.source) :=
  C.source.2.primeIdealOf ⟨s y, C.mem_source⟩

/-- The augmentation kernel lies in the prime at the section point. -/
lemma ker_augmentation_le_sectionPrime :
    RingHom.ker C.augmentation ≤ C.sectionPrime.asIdeal := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE C.source.1 C.source.2
    C.base.1 C.base.2 C.base_le C.mem_base
  change RingHom.ker C.augmentation ≤
    (C.source.2.primeIdealOf ⟨s y, C.base_le C.mem_base⟩).asIdeal
  rw [← h]
  exact Ideal.ker_le_comap C.augmentation

/-- Structure homomorphisms commute with restriction to smaller compatible charts. -/
lemma ringMap_restrict (D : SectionChart f s y)
    (hU : D.base.1 ≤ C.base.1) (hV : D.source.1 ≤ C.source.1) :
    f.appLE C.base C.source C.source_le ≫ X.presheaf.map (homOfLE hV).op =
      S.presheaf.map (homOfLE hU).op ≫ f.appLE D.base D.source D.source_le := by
  simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- Augmentations commute with restriction to smaller compatible charts. -/
lemma augmentation_restrict (D : SectionChart f s y)
    (hU : D.base.1 ≤ C.base.1) (hV : D.source.1 ≤ C.source.1) :
    s.appLE C.source C.base C.base_le ≫ S.presheaf.map (homOfLE hU).op =
      X.presheaf.map (homOfLE hV).op ≫ s.appLE D.source D.base D.base_le := by
  simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

end SectionChart

/-- Shrink a standard smooth chart so that it contains the restricted section. -/
lemma sectionChart_of_standardSmooth (hs : s ≫ f = 𝟙 S) (y : S)
    (U : S.affineOpens) (V : X.affineOpens) (hy : s y ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (hf : RingHom.IsStandardSmoothOfRelativeDimension 1 (f.appLE U V e).hom) :
    ∃ C : SectionChart f s y, C.base.1 ≤ U.1 ∧ C.source.1 ≤ V.1 := by
  have hsy : f (s y) = y := by
    simpa using congrArg (fun g : S ⟶ S ↦ g y) hs
  obtain ⟨r, hr, hyr⟩ := U.2.exists_basicOpen_le
    (⟨y, hy⟩ : s ⁻¹ᵁ V.1) (by simpa [hsy] using e hy)
  let t := f.appLE U V e r
  have ht : X.basicOpen t = V.1 ⊓ f ⁻¹ᵁ S.basicOpen r :=
    Scheme.basicOpen_appLE f V U e r
  have ef : X.basicOpen t ≤ f ⁻¹ᵁ S.basicOpen r := by rw [ht]; exact inf_le_right
  have es : S.basicOpen r ≤ s ⁻¹ᵁ X.basicOpen t := by
    intro z hz
    rw [ht]
    refine ⟨hr hz, ?_⟩
    have hz' : f (s z) = z := by
      simpa using congrArg (fun g : S ⟶ S ↦ g z) hs
    change f (s z) ∈ S.basicOpen r
    rwa [hz']
  have hsm : RingHom.IsStandardSmoothOfRelativeDimension 1
      (f.appLE (S.basicOpen r) (X.basicOpen t) ef).hom := by
    let := U.2.isLocalization_basicOpen r
    let := V.2.isLocalization_basicOpen t
    rw [U.2.appLE_eq_away_map f V.2]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves 1).away
      _ _ _ _ hf
  exact ⟨⟨⟨S.basicOpen r, U.2.basicOpen r⟩, ⟨X.basicOpen t, V.2.basicOpen t⟩,
    hyr, ef, es, hsm⟩, S.basicOpen_le r, X.basicOpen_le t⟩

/-- Compatible section charts can refine prescribed affine neighborhoods. -/
theorem exists_sectionChart_le [SmoothOfRelativeDimension 1 f]
    (hs : s ≫ f = 𝟙 S) (y : S) (U : S.affineOpens) (V : X.affineOpens)
    (hyU : y ∈ U.1) (hyV : s y ∈ V.1) :
    ∃ C : SectionChart f s y, C.base.1 ≤ U.1 ∧ C.source.1 ≤ V.1 := by
  obtain ⟨U₀, hU₀, V₀, hV₀, hy₀, e₀, hf₀⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) (s y)
  have hsy : f (s y) = y := by
    simpa using congrArg (fun g : S ⟶ S ↦ g y) hs
  obtain ⟨r, t, hyt, e, hf⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves 1).away
    (s y) U ⟨U₀, hU₀⟩ V ⟨V₀, hV₀⟩ hyV hy₀ e₀ hf₀ (by simpa [hsy] using hyU)
  obtain ⟨C, hCU, hCV⟩ := sectionChart_of_standardSmooth f s hs y
    ⟨S.basicOpen r, U.2.basicOpen r⟩ ⟨X.basicOpen t, V.2.basicOpen t⟩ hyt e hf
  exact ⟨C, hCU.trans (S.basicOpen_le r), hCV.trans (X.basicOpen_le t)⟩

/-- Every point of the base has a compatible standard smooth section chart. -/
theorem exists_sectionChart [SmoothOfRelativeDimension 1 f]
    (hs : s ≫ f = 𝟙 S) (y : S) : Nonempty (SectionChart f s y) := by
  obtain ⟨U, hU, V, hV, hy, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := f) (s y)
  obtain ⟨C, _, _⟩ := sectionChart_of_standardSmooth f s hs y ⟨U, hU⟩ ⟨V, hV⟩ hy e hf
  exact ⟨C⟩

end FLT.Mazur.FCurve
