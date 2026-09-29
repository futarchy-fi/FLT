/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSectionExtensionCoordinates

/-!
# Localization from pair overlaps to triple intersections

The additional chart cuts out the principal open of `Xᵢ/Xⱼ` on the pair
coordinate spectrum. Coherence identifies restriction with module localization,
and finite families in its kernel are killed by one common coordinate power.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open FLT.Mazur.FCurve

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The additional coordinate on a pair overlap is `Xᵢ/Xⱼ`. -/
def tripleCoordinate (j k i : ι) : overlapRing R ι j k :=
  toOverlap R ι j k (coordinate R ι j i)

/-- Pulling back the additional chart gives precisely its coordinate principal open. -/
lemma overlapMap_preimage_chart (j k i : ι) :
    overlapMap R ι j k ⁻¹ᵁ chart R ι i =
      PrimeSpectrum.basicOpen (tripleCoordinate R ι j k i) := by
  rw [← toOverlap_chartMap, Scheme.Hom.comp_preimage, chartMap_preimage_chart]
  exact SpecMap_preimage_basicOpen _ _

/-- The principal open has image equal to the actual triple intersection. -/
lemma overlapMap_image_triple (j k i : ι) :
    overlapMap R ι j k ''ᵁ PrimeSpectrum.basicOpen (tripleCoordinate R ι j k i) =
      (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i := by
  rw [← overlapMap_preimage_chart]
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange,
    overlapMap_image_top]

/-- The original sections on the principal open, with the overlap-ring action. -/
abbrev tripleSections (F : (space R ι).Modules) (j k i : ι) :
    ModuleCat (overlapRing R ι j k) :=
  (modulesSpecToSheaf.obj (overlapModule R ι F j k)).presheaf.obj
    (op (PrimeSpectrum.basicOpen (tripleCoordinate R ι j k i)))

/-- Pair-to-triple restriction is the actual sheaf restriction in affine coordinates. -/
abbrev overlapTripleRestriction (F : (space R ι).Modules) (j k i : ι) :
    overlapSections R ι F j k →ₗ[overlapRing R ι j k] tripleSections R ι F j k i :=
  specOpenRestriction (overlapModule R ι F j k)
    (PrimeSpectrum.basicOpen (tripleCoordinate R ι j k i))

private lemma triple_specOpenRestriction_localized {A : CommRingCat.{u}}
    (M : (Spec A).Modules) (N : ModuleCat A) (e : M ≅ tilde N) (f : A) :
    IsLocalizedModule (.powers f) (specOpenRestriction M (PrimeSpectrum.basicOpen f)) :=
  isLocalizing_of_iso (modulesSpecToSheaf.mapIso e.symm) (isLocalizing_tilde N) f

/-- Coherence on the pair spectrum gives localization at the specified ratio. -/
instance overlapTripleRestriction_isLocalized (F : (space R ι).Modules)
    [F.IsFinitePresentation] (j k i : ι) :
    IsLocalizedModule (.powers (tripleCoordinate R ι j k i))
      (overlapTripleRestriction R ι F j k i) :=
  triple_specOpenRestriction_localized (overlapModule R ι F j k)
    (overlapSections R ι F j k) (coherentAffineChartIso (overlapMap R ι j k) F)
    (tripleCoordinate R ι j k i)

/-- Principal-open sections identified with sections on the ambient triple intersection. -/
def tripleSectionsIso (F : (space R ι).Modules) (j k i : ι) :
    Γ(overlapModule R ι F j k,
      PrimeSpectrum.basicOpen (tripleCoordinate R ι j k i)) ≅
      Γ(F, (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i) :=
  F.restrictAppIso (overlapMap R ι j k) _ ≪≫
    F.presheaf.mapIso (eqToIso (overlapMap_image_triple R ι j k i).symm).op

/-- The affine-coordinate restriction is exactly restriction of the ambient sheaf. -/
lemma tripleSectionsIso_restriction (F : (space R ι).Modules) (j k i : ι)
    (s : overlapSections R ι F j k) :
    (tripleSectionsIso R ι F j k i).hom (overlapTripleRestriction R ι F j k i s) =
      F.presheaf.map (homOfLE inf_le_left).op ((overlapSectionsIso R ι F j k).hom s) := by
  change F.presheaf.map _ (F.presheaf.map _ s) =
    F.presheaf.map _ (F.presheaf.map _ s)
  simp only [← Functor.map_comp_apply]
  congr 1

/-- Vanishing on the triple intersection is detected by powers of `Xᵢ/Xⱼ`. -/
lemma overlapTriple_zero_iff (F : (space R ι).Modules) [F.IsFinitePresentation]
    (j k i : ι) (s : overlapSections R ι F j k) :
    overlapTripleRestriction R ι F j k i s = 0 ↔
      ∃ n : ℕ, tripleCoordinate R ι j k i ^ n • s = 0 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq
      (tripleCoordinate R ι j k i) (f := overlapTripleRestriction R ι F j k i)
      (h.trans (map_zero _).symm)
    exact ⟨n, by simpa only [smul_zero] using hn⟩
  · rintro ⟨n, hn⟩
    rw [← map_zero (overlapTripleRestriction R ι F j k i)]
    exact (IsLocalizedModule.eq_iff_exists (.powers (tripleCoordinate R ι j k i))
      (overlapTripleRestriction R ι F j k i)).mpr
      ⟨⟨_, n, rfl⟩, by simpa only [Submonoid.smul_def, smul_zero] using hn⟩

/-- Structure-sheaf scalars on the triple open induced by its coordinate spectrum. -/
def tripleScalarHom (j k i : ι) : overlapRing R ι j k →+*
    Γ(space R ι, (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i) :=
  (((Scheme.ΓSpecIso (.of (overlapRing R ι j k))).inv ≫
    (Spec (.of (overlapRing R ι j k))).presheaf.map
      (PrimeSpectrum.basicOpen (tripleCoordinate R ι j k i)).leTop.op ≫
    ((overlapMap R ι j k).appIso _).inv) ≫
    (space R ι).presheaf.map
      (eqToHom (overlapMap_image_triple R ι j k i).symm).op).hom

/-- The triple scalar map is restriction of the pair scalar map used in 6b. -/
lemma tripleScalarHom_eq (j k i : ι) :
    tripleScalarHom R ι j k i =
      ((space R ι).presheaf.map (homOfLE inf_le_left).op).hom.comp
        (overlapScalarHom R ι j k) := by
  unfold tripleScalarHom overlapScalarHom
  simp only [Category.assoc, Scheme.Hom.appIso_inv_naturality_assoc]
  simp only [← Functor.map_comp, ← Category.assoc]
  rfl

/-- The triple section comparison carries the explicitly specified scalar action. -/
lemma tripleSectionsIso_smul (F : (space R ι).Modules) (j k i : ι)
    (r : overlapRing R ι j k) (s : tripleSections R ι F j k i) :
    (tripleSectionsIso R ι F j k i).hom (r • s) =
      tripleScalarHom R ι j k i r • (tripleSectionsIso R ι F j k i).hom s := by
  exact F.val.map_smul (eqToHom (overlapMap_image_triple R ι j k i).symm).op _ s

/-- Ambient pair sections carry the coordinate action via the established scalar map. -/
instance ambientPairModule (F : (space R ι).Modules) (j k : ι) :
    Module (overlapRing R ι j k) Γ(F, chart R ι j ⊓ chart R ι k) :=
  Module.compHom _ (overlapScalarHom R ι j k)

/-- Ambient triple sections carry scalars via restriction of the pair scalar map. -/
instance ambientTripleModule (F : (space R ι).Modules) (j k i : ι) :
    Module (overlapRing R ι j k) Γ(F, (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i) :=
  Module.compHom _ (tripleScalarHom R ι j k i)

/-- The pair comparison is linear over the overlap coordinate ring. -/
def ambientPairEquiv (F : (space R ι).Modules) (j k : ι) :
    overlapSections R ι F j k ≃ₗ[overlapRing R ι j k]
      Γ(F, chart R ι j ⊓ chart R ι k) where
  __ := (overlapSectionsIso R ι F j k).addCommGroupIsoToAddEquiv
  map_smul' := overlapSectionsIso_smul R ι F j k

/-- The triple comparison is linear over the same overlap coordinate ring. -/
def ambientTripleEquiv (F : (space R ι).Modules) (j k i : ι) :
    tripleSections R ι F j k i ≃ₗ[overlapRing R ι j k]
      Γ(F, (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i) where
  __ := (tripleSectionsIso R ι F j k i).addCommGroupIsoToAddEquiv
  map_smul' := tripleSectionsIso_smul R ι F j k i

/-- The ordinary ambient restriction, linear for the specified coordinate action. -/
def ambientTripleRestriction (F : (space R ι).Modules) (j k i : ι) :
    Γ(F, chart R ι j ⊓ chart R ι k) →ₗ[overlapRing R ι j k]
      Γ(F, (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i) where
  __ := (F.presheaf.map (homOfLE inf_le_left).op).hom
  map_smul' r s := by
    change F.presheaf.map _ (overlapScalarHom R ι j k r • s) =
      tripleScalarHom R ι j k i r • _
    rw [tripleScalarHom_eq]
    exact F.val.map_smul _ _ _

/-- Transporting affine localization gives localization of actual ambient restriction. -/
instance ambientTripleRestriction_isLocalized (F : (space R ι).Modules)
    [F.IsFinitePresentation] (j k i : ι) :
    IsLocalizedModule (.powers (tripleCoordinate R ι j k i))
      (ambientTripleRestriction R ι F j k i) := by
  have he : ambientTripleRestriction R ι F j k i =
      (ambientTripleEquiv R ι F j k i).toLinearMap.comp
        ((overlapTripleRestriction R ι F j k i).comp
          (ambientPairEquiv R ι F j k).symm.toLinearMap) := by
    ext s
    exact (tripleSectionsIso_restriction R ι F j k i
      ((ambientPairEquiv R ι F j k).symm s)).trans
        (congrArg (F.presheaf.map (homOfLE inf_le_left).op)
          ((ambientPairEquiv R ι F j k).apply_symm_apply s)) |>.symm
  rw [he]
  infer_instance

variable {κ : Type v} [Finite κ]

/-- One exponent kills a finite family on pair overlaps vanishing on the triple opens. -/
theorem tripleFamily_annihilateKernels (F : (space R ι).Modules)
    [F.IsFinitePresentation] (j k i : κ → ι)
    (s : ∀ t, overlapSections R ι F (j t) (k t))
    (h : ∀ t, overlapTripleRestriction R ι F (j t) (k t) (i t) (s t) = 0) :
    ∃ m : ℕ, ∀ t, tripleCoordinate R ι (j t) (k t) (i t) ^ m • s t = 0 := by
  classical
  let := Fintype.ofFinite κ
  choose n hn using fun t ↦
    (overlapTriple_zero_iff R ι F (j t) (k t) (i t) (s t)).mp (h t)
  refine ⟨Finset.univ.sup n, fun t ↦ ?_⟩
  have ht : n t ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ t)
  simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel ht, smul_zero] using
    congrArg (fun x : overlapSections R ι F (j t) (k t) ↦
      tripleCoordinate R ι (j t) (k t) (i t) ^ (Finset.univ.sup n - n t) • x) (hn t)

/-- The same uniform annihilation for ambient sections and structure-sheaf scalars. -/
theorem tripleFamily_annihilateKernels_ambient (F : (space R ι).Modules)
    [F.IsFinitePresentation] (j k i : κ → ι)
    (s : ∀ t, Γ(F, chart R ι (j t) ⊓ chart R ι (k t)))
    (h : ∀ t, F.presheaf.map
      (homOfLE (show (chart R ι (j t) ⊓ chart R ι (k t)) ⊓ chart R ι (i t) ≤
        chart R ι (j t) ⊓ chart R ι (k t) from inf_le_left)).op (s t) = 0) :
    ∃ m : ℕ, ∀ t,
      overlapScalarHom R ι (j t) (k t)
        (toOverlap R ι (j t) (k t) (coordinate R ι (j t) (i t))) ^ m • s t = 0 := by
  let s' := fun t ↦ (ambientPairEquiv R ι F (j t) (k t)).symm (s t)
  have hz (t : κ) : overlapTripleRestriction R ι F (j t) (k t) (i t) (s' t) = 0 := by
    apply (ambientTripleEquiv R ι F (j t) (k t) (i t)).injective
    rw [map_zero]
    change (tripleSectionsIso R ι F (j t) (k t) (i t)).hom _ = 0
    rw [tripleSectionsIso_restriction]
    change F.presheaf.map _ ((ambientPairEquiv R ι F (j t) (k t))
      ((ambientPairEquiv R ι F (j t) (k t)).symm (s t))) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact h t
  obtain ⟨m, hm⟩ := tripleFamily_annihilateKernels R ι F j k i s' hz
  refine ⟨m, fun t ↦ ?_⟩
  have ht := congrArg (overlapSectionsIso R ι F (j t) (k t)).hom (hm t)
  rw [overlapSectionsIso_smul, map_pow, map_zero] at ht
  change overlapScalarHom R ι (j t) (k t) (tripleCoordinate R ι (j t) (k t) (i t)) ^ m •
    (ambientPairEquiv R ι F (j t) (k t))
      ((ambientPairEquiv R ι F (j t) (k t)).symm (s t)) = 0 at ht
  simpa only [tripleCoordinate, LinearEquiv.apply_symm_apply] using ht

/-- For all pairs of a finite chart cover, a fixed third chart gives one exponent. -/
theorem pairFamily_annihilateKernels_ambient [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i : ι)
    (s : ∀ j k, Γ(F, chart R ι j ⊓ chart R ι k))
    (h : ∀ j k, F.presheaf.map
      (homOfLE (show (chart R ι j ⊓ chart R ι k) ⊓ chart R ι i ≤
        chart R ι j ⊓ chart R ι k from inf_le_left)).op (s j k) = 0) :
    ∃ m : ℕ, ∀ j k,
      overlapScalarHom R ι j k (toOverlap R ι j k (coordinate R ι j i)) ^ m • s j k = 0 := by
  obtain ⟨m, hm⟩ := tripleFamily_annihilateKernels_ambient R ι F
    (κ := ι × ι) Prod.fst Prod.snd (fun _ ↦ i) (fun t ↦ s t.1 t.2) (fun t ↦ h t.1 t.2)
  exact ⟨m, fun j k ↦ hm (j, k)⟩

end FLT.Mazur.ProjectiveSpace
