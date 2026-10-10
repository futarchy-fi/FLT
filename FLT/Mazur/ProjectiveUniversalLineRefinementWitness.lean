/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUniversalLineComparison

/-!
# Canonical geometric refinement of universal overlaps

The actual extended submodules construct the refined isomorphism. Its forward
map is proved to be the pullback of the original overlap map, transported
through canonical geometric comparisons to the specified chart maps.
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

/-- Equal coefficient paths give the actual affine scheme composition square. -/
lemma universalLine_spec_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (χ : B →+* C) (ψ : A →+* C) (h : χ.comp φ = ψ) :
    Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom ψ) := by
  rw [← h, CommRingCat.ofHom_comp, Spec.map_comp]

/-- Ring path equalities identify the actual extended universal submodules. -/
lemma universalLineRefinement_val (i j : ι) (χ : overlapRing R ι i j →+* S)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S)
    (hφ : χ.comp (chartOverlapLeft R ι i j).toRingHom = φ)
    (hψ : χ.comp (chartOverlapRight R ι i j).toRingHom = ψ) :
    (baseChange φ i (universalChartLine R ι i)).val =
      (baseChange ψ j (universalChartLine R ι j)).val := by
  subst φ ψ
  exact universalChartLine_refine_val R ι i j χ

/-- Refinement to specified chart maps, constructed from the actual extended submodules. -/
def universalLineRefinement (i j : ι) (χ : overlapRing R ι i j →+* S)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S)
    (hφ : χ.comp (chartOverlapLeft R ι i j).toRingHom = φ)
    (hψ : χ.comp (chartOverlapRight R ι i j).toRingHom = ψ) :
    (pullback (Spec.map (CommRingCat.ofHom φ))).obj (universalChartLineSheaf R ι i) ≅
      (pullback (Spec.map (CommRingCat.ofHom ψ))).obj (universalChartLineSheaf R ι j) :=
  universalLineCompare R ι i j φ ψ (universalLineRefinement_val R ι i j χ φ ψ hφ hψ)

attribute [local irreducible] compositeIso Scheme.Modules.pullback universalLineCompare
attribute [local irreducible] universalChartLineOverlap universalChartLine

/-- Refinement agrees with the direct inclusion-preserving comparison. -/
lemma universalLineRefinement_eq (i j : ι) (χ : overlapRing R ι i j →+* S)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S)
    (hφ : χ.comp (chartOverlapLeft R ι i j).toRingHom = φ)
    (hψ : χ.comp (chartOverlapRight R ι i j).toRingHom = ψ)
    (h : (baseChange φ i (universalChartLine R ι i)).val =
      (baseChange ψ j (universalChartLine R ι j)).val) :
    universalLineRefinement R ι i j χ φ ψ hφ hψ = universalLineCompare R ι i j φ ψ h := rfl

/-- Its forward map is the original overlap map pulled back through geometric comparisons. -/
lemma universalLineRefinement_comp_hom [Finite ι] (i j : ι)
    (χ : overlapRing R ι i j →+* S)
    (wφ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom (χ.comp (chartOverlapLeft R ι i j).toRingHom)))
    (wψ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom (χ.comp (chartOverlapRight R ι i j).toRingHom))) :
    (universalLineRefinement R ι i j χ
        (χ.comp (chartOverlapLeft R ι i j).toRingHom)
        (χ.comp (chartOverlapRight R ι i j).toRingHom) rfl rfl).hom =
      (compositeIso _ _ _ wφ (universalChartLineSheaf R ι i)).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom χ))).map (universalLineOverlapMap R ι i j) ≫
          (compositeIso _ _ _ wψ (universalChartLineSheaf R ι j)).hom :=
  (universalLineCompare_refine R ι i j χ wφ wψ).symm

/-- The formula also holds at specified chart maps with proved coefficient path identities. -/
lemma universalLineRefinement_hom [Finite ι] (i j : ι)
    (χ : overlapRing R ι i j →+* S)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S)
    (wφ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapLeft R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom φ))
    (wψ : Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (chartOverlapRight R ι i j).toRingHom) =
      Spec.map (CommRingCat.ofHom ψ))
    (hφ : χ.comp (chartOverlapLeft R ι i j).toRingHom = φ)
    (hψ : χ.comp (chartOverlapRight R ι i j).toRingHom = ψ) :
    (universalLineRefinement R ι i j χ φ ψ hφ hψ).hom =
      (compositeIso _ _ _ wφ (universalChartLineSheaf R ι i)).inv ≫
        (pullback (Spec.map (CommRingCat.ofHom χ))).map (universalLineOverlapMap R ι i j) ≫
          (compositeIso _ _ _ wψ (universalChartLineSheaf R ι j)).hom := by
  subst φ ψ
  exact universalLineRefinement_comp_hom R ι i j χ wφ wψ

/-- Refinement preserves the original ambient inclusion after coefficient extension. -/
lemma universalLineRefinement_inclusion [Finite ι] (i j : ι)
    (χ : overlapRing R ι i j →+* S)
    (φ : chartRing R ι i →+* S) (ψ : chartRing R ι j →+* S) (hφ) (hψ) :
    (universalLineRefinement R ι i j χ φ ψ hφ hψ).hom ≫
        universalLinePullbackInclusion R ι j ψ = universalLinePullbackInclusion R ι i φ :=
  universalLineCompare_inclusion R ι i j φ ψ _

end FLT.Mazur.ProjectiveSpace
