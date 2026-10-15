/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperNeighborhoodEnvelopeInterior
public import FLT.Mazur.PartialCompactTranslationInterior

/-!
# Constructed partial translation charts over the fixed ground

Proper open neighborhoods of the excluded translation coordinates construct
actual independent product charts. Their projections are proper by Cartesian
base change. Compactness of the excluded envelope extracts a finite family;
neither a supplied chart family nor finite free section bases are required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open SchemeOpenEnvelope
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (B W : Over S)

/-- The canonical translation charts retain their actual original ground morphisms. -/
def properTranslationChart (i : ProperNeighborhoodAtlas.Index W.hom) : Over S :=
  Over.mk (i.val.ι ≫ W.hom)

/-- The canonical chart map is the actual open inclusion over the unchanged ground. -/
def properTranslationInclusion (i : ProperNeighborhoodAtlas.Index W.hom) :
    properTranslationChart W i ⟶ W := Over.homMk i.val.ι

instance properTranslationChart_isProper (i : ProperNeighborhoodAtlas.Index W.hom) :
    IsProper (properTranslationChart W i).hom := i.property

instance properTranslationInclusion_isOpenImmersion
    (i : ProperNeighborhoodAtlas.Index W.hom) :
    IsOpenImmersion (properTranslationInclusion W i).left :=
  inferInstanceAs (IsOpenImmersion i.val.ι)

/-- Independent envelope charts are actual open immersions, not selected residue branches. -/
theorem properTranslationEnvelope_isOpenImmersion (i : ProperNeighborhoodAtlas.Index W.hom) :
    IsOpenImmersion (prod.map (𝟙 B) (properTranslationInclusion W i)).left :=
  MorphismProperty.of_isPullback
    ((HilbertChart.AffineRestriction.translationProductRight_isPullback
      (B := B) (properTranslationInclusion W i)).map (Over.forget _))
    (inferInstanceAs (IsOpenImmersion (properTranslationInclusion W i).left))

/-- Every constructed chart projection is proper over the original source. -/
theorem properTranslationEnvelope_projection_isProper
    (i : ProperNeighborhoodAtlas.Index W.hom) :
    IsProper (prod.fst : prod B (properTranslationChart W i) ⟶ B).left :=
  MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B (properTranslationChart W i))).flip
    (inferInstanceAs (IsProper (properTranslationChart W i).hom))

variable (U : (prod B W).left.Opens)
  (hU : IsCompact (U : Set (prod B W).left)ᶜ)
  (hproper : ∀ y : (prod B W).left, y ∉ U →
    (prod.snd : prod B W ⟶ W).left y ∈ ProperNeighborhoodAtlas.locus W.hom)
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "E" => fun i ↦ Over.left (prod B (properTranslationChart W i))
local notation "g" => fun i ↦ Over.Hom.left (prod.map (𝟙 B) (properTranslationInclusion W i))

include hproper

/-- The constructed independent charts cover every excluded envelope point exactly. -/
theorem properTranslationEnvelope_partialCover (y : (prod B W).left) (hy : y ∉ U) :
    ∃ i, ∃ z : E i, g i z = y := by
  obtain ⟨i, z, hz⟩ := (ProperNeighborhoodAtlas.covers W.hom _).mpr (hproper y hy)
  have H := (HilbertChart.AffineRestriction.translationProductRight_isPullback
    (B := B) (properTranslationInclusion W i)).map (Over.forget _)
  obtain ⟨e, he, _⟩ := Scheme.exists_preimage_of_isPullback H.flip y z hz.symm
  exact ⟨i, e, he⟩

include hU

/-- Compactness constructs finitely many independent charts covering the entire excluded locus. -/
theorem exists_properTranslationEnvelope_partialCover :
    ∃ J : Finset (ProperNeighborhoodAtlas.Index W.hom),
      ∀ y : (prod B W).left, y ∉ U → ∃ i ∈ J, ∃ z : E i, g i z = y := by
  apply exists_finite_partialCover E g U hU
  · intro i
    let _ := properTranslationEnvelope_isOpenImmersion B W i
    exact (g i).isOpenMap.isOpen_range
  · exact properTranslationEnvelope_partialCover B W U hproper

/-- Constructed proper translation neighborhoods suffice for the full original fiber open. -/
theorem isOpen_fullFiber_of_properTranslationNeighborhoods :
    IsOpen (fullFiberLocus π U) := by
  apply isOpen_fullFiber_of_compact_partialClosedCover π E g U
    (properTranslationEnvelope_partialCover B W U hproper) hU
  · intro i
    let _ := properTranslationEnvelope_isOpenImmersion B W i
    exact (g i).isOpenMap.isOpen_range
  · intro i
    have he : g i ≫ π =
        (prod.fst : prod B (properTranslationChart W i) ⟶ B).left := by
      have h := congrArg Over.Hom.left
        (prod.map_fst (𝟙 B) (properTranslationInclusion W i))
      simpa only [Over.comp_left, Category.comp_id] using h
    rw [he]
    let _ := properTranslationEnvelope_projection_isProper B W i
    exact (prod.fst : prod B (properTranslationChart W i) ⟶ B).left.isClosedMap

end FLT.Mazur.SchemeTranslationNorm
