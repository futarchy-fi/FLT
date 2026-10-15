/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenEnvelopeLocus
public import FLT.Mazur.UnramifiedSectionImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Whole-fiber neighborhoods covered by actual finite étale sections

Finitely many sections covering one fiber of a finite étale map cover every
fiber in a constructed affine base neighborhood. Restricting the sections
produces actual maps covering the entire restricted source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FiniteEtaleSectionCoverNeighborhood
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- Restrict an actual section to an arbitrary base open, retaining its whole inverse image. -/
def restrictedSection (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) (U : Y.Opens) :
    U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  s.resLE (p ⁻¹ᵁ U) U (by
    intro y hy
    change p (s y) ∈ U
    rw [← Scheme.Hom.comp_apply, hs]
    exact hy)

/-- The restricted section keeps its original source coordinate exactly. -/
@[reassoc]
theorem restrictedSection_ι (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) (U : Y.Opens) :
    restrictedSection p s hs U ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ s :=
  Scheme.Hom.resLE_comp_ι _ _

/-- Restriction preserves the actual section identity. -/
@[reassoc]
theorem restrictedSection_section (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) (U : Y.Opens) :
    restrictedSection p s hs U ≫ (p ∣_ U) = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, restrictedSection_ι,
    Category.assoc, hs, Category.comp_id, Category.id_comp]

/-- Coverage over an open is coverage by the actual restricted sections. -/
theorem restrictedSection_covers {n : ℕ} (s : Fin n → (Y ⟶ X))
    (hs : ∀ i, s i ≫ p = 𝟙 Y) (U : Y.Opens)
    (h : ∀ x : X, p x ∈ U → ∃ i, s i (p x) = x) :
    ∀ x : (p ⁻¹ᵁ U).toScheme,
      ∃ i, restrictedSection p (s i) (hs i) U ((p ∣_ U) x) = x := by
  intro x
  obtain ⟨i, hi⟩ := h x.val x.property
  refine ⟨i, ?_⟩
  apply (p ⁻¹ᵁ U).ι.isOpenEmbedding.injective
  change ((restrictedSection p (s i) (hs i) U) ≫ (p ⁻¹ᵁ U).ι) ((p ∣_ U) x) = x.val
  rw [restrictedSection_ι]
  change s i (((p ∣_ U) ≫ U.ι) x) = x.val
  rw [morphismRestrict_ι]
  exact hi

/-- Covering one full fiber constructs an affine neighborhood covered by restricted sections. -/
theorem exists_affine_section_cover [IsFinite p] [Etale p]
    {n : ℕ} (s : Fin n → (Y ⟶ X)) (hs : ∀ i, s i ≫ p = 𝟙 Y)
    (y : Y) (hy : ∀ x : X, p x = y → ∃ i, s i y = x) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧
      ∀ x : (p ⁻¹ᵁ U).toScheme,
        ∃ i, restrictedSection p (s i) (hs i) U ((p ∣_ U) x) = x := by
  let _ (i : Fin n) : IsOpenImmersion (s i) :=
    UnramifiedSectionImmersion.isOpenImmersion p (s i) (hs i)
  let O : X.Opens := ⨆ i, (s i).opensRange
  let B := SchemeOpenEnvelope.fullFiberOpen p O p.isClosedMap
  have hyB : y ∈ B := by
    apply (SchemeOpenEnvelope.mem_fullFiberLocus p O y).mpr
    intro x hx
    obtain ⟨i, hi⟩ := hy x hx
    exact Opens.mem_iSup.mpr ⟨i, y, hi⟩
  obtain ⟨U, hU, hyU, hUB⟩ := exists_isAffineOpen_mem_and_subset hyB
  refine ⟨U, hU, hyU, restrictedSection_covers p s hs U ?_⟩
  intro x hx
  have hxO : x ∈ O := SchemeOpenEnvelope.preimage_fullFiberOpen_le p O p.isClosedMap
    (hUB hx)
  obtain ⟨i, w, hw⟩ := Opens.mem_iSup.mp hxO
  have hw' : w = p x := by
    calc
      w = (s i ≫ p) w := by rw [hs]; rfl
      _ = p x := congrArg p hw
  exact ⟨i, hw' ▸ hw⟩

end FLT.Mazur.FiniteEtaleSectionCoverNeighborhood
