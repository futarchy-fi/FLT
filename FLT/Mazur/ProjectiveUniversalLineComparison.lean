/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUniversalLineTriplePaths
public import FLT.Mazur.NormalizedSectionLineRefinedInclusion

/-!
# Comparing actual universal line pullbacks

Equal coordinate submodules determine a unique comparison between actual
pullback line sheaves preserving the ambient inclusions. This uniqueness
proves the cocycle and identifies refinements of the original overlap map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open NormalizedSectionLine AffineIteratedPullbackSections
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S : Type u} [CommRing S]

/-- The actual pullback inclusion, with its ambient coefficient comparison. -/
def universalLinePullbackInclusion [Finite ι] (i : ι) (φ : chartRing R ι i →+* S) :=
  (pullback (Spec.map (CommRingCat.ofHom φ))).map (universalChartLineInclusion R ι i) ≫
    (vectorSheafBaseChange ι φ).hom

instance [Finite ι] (i : ι) (φ : chartRing R ι i →+* S) :
    Mono (universalLinePullbackInclusion R ι i φ) := by
  dsimp only [universalLinePullbackInclusion]
  infer_instance

/-- Comparison of the actual pullbacks classified by equal line submodules. -/
def universalLineCompare (i j : ι) (φ : chartRing R ι i →+* S)
    (ψ : chartRing R ι j →+* S)
    (h : (baseChange φ i (universalChartLine R ι i)).val =
      (baseChange ψ j (universalChartLine R ι j)).val) :
    (pullback (Spec.map (CommRingCat.ofHom φ))).obj (universalChartLineSheaf R ι i) ≅
      (pullback (Spec.map (CommRingCat.ofHom ψ))).obj (universalChartLineSheaf R ι j) :=
  universalChartLinePullback R ι i φ ≪≫ sheafChartChange i j _ _ h ≪≫
    (universalChartLinePullback R ι j ψ).symm

attribute [local irreducible] universalChartLinePullback sheafChartChange
attribute [local irreducible] vectorSheafBaseChange Scheme.Modules.pullback compositeIso

/-- The comparison preserves the original pullback inclusion. -/
lemma universalLineCompare_inclusion [Finite ι] (i j : ι)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S) (h) :
    (universalLineCompare R ι i j φ ψ h).hom ≫ universalLinePullbackInclusion R ι j ψ =
      universalLinePullbackInclusion R ι i φ := by
  dsimp only [universalLinePullbackInclusion]
  rw [← universalChartLinePullback_inclusion, ← universalChartLinePullback_inclusion]
  simp only [universalLineCompare, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, sheafChartChange_inclusion]

/-- The actual ambient inclusion determines the comparison uniquely. -/
lemma universalLineCompare_unique [Finite ι] (i j : ι)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S) (h)
    (a : (pullback (Spec.map (CommRingCat.ofHom φ))).obj (universalChartLineSheaf R ι i) ⟶
      (pullback (Spec.map (CommRingCat.ofHom ψ))).obj (universalChartLineSheaf R ι j))
    (ha : a ≫ universalLinePullbackInclusion R ι j ψ =
      universalLinePullbackInclusion R ι i φ) :
    a = (universalLineCompare R ι i j φ ψ h).hom := by
  apply (cancel_mono (universalLinePullbackInclusion R ι j ψ)).mp
  rw [ha, universalLineCompare_inclusion]

/-- These comparisons form a cocycle between actual pullback sheaves. -/
lemma universalLineCompare_cocycle [Finite ι] (i j k : ι)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S)
    (χ : chartRing R ι k →+* S) (h) (h') :
    universalLineCompare R ι i j φ ψ h ≪≫ universalLineCompare R ι j k ψ χ h' =
      universalLineCompare R ι i k φ χ (h.trans h') := by
  apply Iso.ext
  apply universalLineCompare_unique
  simp only [Iso.trans_hom, Category.assoc, universalLineCompare_inclusion]

attribute [local irreducible] universalChartLineOverlap universalLineCompare
attribute [local irreducible] universalChartLine

/-- A sealed copy of the original overlap comparison for geometric refinement. -/
@[irreducible] def universalLineOverlapMap (i j : ι) :
    (pullback (Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom))).obj
        (universalChartLineSheaf R ι i) ⟶
      (pullback (Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom))).obj
        (universalChartLineSheaf R ι j) :=
  (universalChartLineOverlap R ι i j).hom

/-- The sealed comparison is the original overlap map. -/
lemma universalLineOverlapMap_eq (i j : ι) :
    universalLineOverlapMap R ι i j = (universalChartLineOverlap R ι i j).hom := by
  unfold universalLineOverlapMap
  rfl

/-- Refining the original homogeneous overlap preserves the actual inclusion. -/
lemma universalChartLineOverlap_refine_inclusion [Finite ι] (i j : ι)
    (χ : overlapRing R ι i j →+* S)
    (w₁ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom (χ.comp (chartOverlapLeft R ι i j).toRingHom)))
    (w₂ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom (χ.comp (chartOverlapRight R ι i j).toRingHom))) :
    (compositeIso _ _ _ w₁ (universalChartLineSheaf R ι i)).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom χ))).map (universalLineOverlapMap R ι i j) ≫
        (compositeIso _ _ _ w₂ (universalChartLineSheaf R ι j)).hom ≫
        (pullback (Spec.map (CommRingCat.ofHom
          (χ.comp (chartOverlapRight R ι i j).toRingHom)))).map
          (universalChartLineInclusion R ι j) ≫
        (vectorSheafBaseChange ι (χ.comp (chartOverlapRight R ι i j).toRingHom)).hom =
      (pullback (Spec.map (CommRingCat.ofHom
          (χ.comp (chartOverlapLeft R ι i j).toRingHom)))).map
          (universalChartLineInclusion R ι i) ≫
        (vectorSheafBaseChange ι (χ.comp (chartOverlapLeft R ι i j).toRingHom)).hom := by
  rw [← Category.assoc (compositeIso _ _ _ w₂ (universalChartLineSheaf R ι j)).hom,
    pullbackComposition_hom_naturality]
  simp only [Category.assoc]
  rw [vectorSheafBaseChange_comp_hom]
  simp only [← Functor.map_comp_assoc, universalLineOverlapMap_eq,
    universalChartLineOverlap_inclusion]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [pullbackComposition_inv_naturality]
  simp only [Category.assoc]
  rw [vectorSheafBaseChange_comp]

/-- Refinement agrees with the unique direct comparison. -/
lemma universalLineCompare_refine [Finite ι] (i j : ι) (χ : overlapRing R ι i j →+* S)
    (w₁ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom (χ.comp (chartOverlapLeft R ι i j).toRingHom)))
    (w₂ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom (χ.comp (chartOverlapRight R ι i j).toRingHom))) :
    (compositeIso _ _ _ w₁ (universalChartLineSheaf R ι i)).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom χ))).map (universalLineOverlapMap R ι i j) ≫
        (compositeIso _ _ _ w₂ (universalChartLineSheaf R ι j)).hom =
      (universalLineCompare R ι i j
        (χ.comp (chartOverlapLeft R ι i j).toRingHom)
        (χ.comp (chartOverlapRight R ι i j).toRingHom)
        (universalChartLine_refine_val R ι i j χ)).hom := by
  apply universalLineCompare_unique
  dsimp only [universalLinePullbackInclusion]
  simp only [Category.assoc]
  exact universalChartLineOverlap_refine_inclusion R ι i j χ w₁ w₂

end FLT.Mazur.ProjectiveSpace
