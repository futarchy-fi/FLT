/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNegationOverlap

/-! # Gluing the Weierstrass negation morphism

The two local formulas glue on a refinement of the infinity chart and then on
the original two-chart cover. The resulting global morphism preserves the base.
Global involutivity and preservation of the infinity section are separate steps. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The two principal opens refining the infinity chart for negation. -/
def negationInfinityOpen (b : Bool) : Scheme.{u} :=
  if b then Spec (.of (NegationNeighborhood W)) else Spec (.of (Overlap W true))

/-- Inclusion of each principal open into the infinity chart. -/
def negationInfinityInclusion (b : Bool) : negationInfinityOpen W b ⟶ chart W true := by
  cases b
  · exact overlapInclusion W true
  · exact Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (NegationNeighborhood W)))

instance negationInfinityInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (negationInfinityInclusion W b) := by
  cases b
  · exact overlapInclusion_isOpenImmersion W true
  · exact IsOpenImmersion.of_isLocalization (infinityNegationDenominator W)

/-- The ordinary overlap and the negation neighborhood cover the infinity chart. -/
def negationInfinityCover : (chart W true).OpenCover where
  I₀ := Bool
  X := negationInfinityOpen W
  f := negationInfinityInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    by_cases hv : coord W true 1 ∈ x.asIdeal
    · have hd : infinityNegationDenominator W ∉ x.asIdeal := by
        intro hd
        apply x.isPrime.ne_top
        apply top_unique
        rw [← infinity_negation_span W]
        apply Ideal.span_le.mpr
        rintro y (rfl | hy)
        · exact hv
        · rcases Set.mem_singleton_iff.mp hy with rfl
          exact hd
      have hr := PrimeSpectrum.localization_away_comap_range (NegationNeighborhood W)
        (infinityNegationDenominator W)
      obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr hd
      exact ⟨true, y, hy⟩
    · obtain ⟨y, hy⟩ := (Set.ext_iff.mp (overlapInclusion_range W true) x).mpr hv
      exact ⟨false, y, hy⟩

/-- The two local negation maps on the refined infinity cover. -/
def negationInfinityPiece (b : Bool) : negationInfinityOpen W b ⟶ scheme W := by
  cases b
  · exact Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) ≫
      affineNegation W ≫ affineChart W
  · exact infinityNegationMorphism W ≫ infinityChart W

theorem negationInfinityPiece_agreement :
    pullback.fst (negationInfinityInclusion W false) (negationInfinityInclusion W true) ≫
        negationInfinityPiece W false =
      pullback.snd _ _ ≫ negationInfinityPiece W true := by
  let e := (negation_refined_isPullback W).isoPullback
  apply (cancel_epi e.hom).mp
  change e.hom ≫ pullback.fst _ _ ≫
      (Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) ≫
        affineNegation W ≫ affineChart W) =
    e.hom ≫ pullback.snd _ _ ≫ (infinityNegationMorphism W ≫ infinityChart W)
  simp only [e, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  exact negation_refined_overlap_agreement W

theorem negationInfinityPiece_gluing (b c : Bool) :
    pullback.fst (negationInfinityInclusion W b) (negationInfinityInclusion W c) ≫
        negationInfinityPiece W b =
      pullback.snd _ _ ≫ negationInfinityPiece W c := by
  cases b <;> cases c
  · have h : pullback.fst (negationInfinityInclusion W false) (negationInfinityInclusion W false) =
        pullback.snd _ _ :=
      (cancel_mono (negationInfinityInclusion W false)).mp pullback.condition
    rw [h]
  · exact negationInfinityPiece_agreement W
  · apply (cancel_epi
      (pullbackSymmetry (negationInfinityInclusion W false)
        (negationInfinityInclusion W true)).hom).mp
    simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc] using
      (negationInfinityPiece_agreement W).symm
  · have h : pullback.fst (negationInfinityInclusion W true) (negationInfinityInclusion W true) =
        pullback.snd _ _ :=
      (cancel_mono (negationInfinityInclusion W true)).mp pullback.condition
    rw [h]

/-- Negation on the whole infinity chart, obtained by gluing its refined cover. -/
def infinityNegationGlued : chart W true ⟶ scheme W :=
  (negationInfinityCover W).glueMorphisms (negationInfinityPiece W) (negationInfinityPiece_gluing W)

@[reassoc (attr := simp)] theorem overlap_infinityNegationGlued :
    overlapInclusion W true ≫ infinityNegationGlued W =
      Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) ≫
        affineNegation W ≫ affineChart W :=
  (negationInfinityCover W).ι_glueMorphisms _ _ false

@[reassoc (attr := simp)] theorem neighborhood_infinityNegationGlued :
    Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (NegationNeighborhood W))) ≫
        infinityNegationGlued W = infinityNegationMorphism W ≫ infinityChart W :=
  (negationInfinityCover W).ι_glueMorphisms _ _ true

theorem negation_gluing :
    overlapInclusion W false ≫ (affineNegation W ≫ affineChart W) =
      overlapRight W ≫ infinityNegationGlued W := by
  have hc : (overlapIso W).hom ≫
      Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) =
        overlapInclusion W false := by
    apply (cancel_mono (affineChart W)).mp
    rw [Category.assoc, changeChart_true_to_scheme]
    exact (overlap_condition W).symm
  unfold overlapRight
  rw [Category.assoc, overlap_infinityNegationGlued]
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ f ≫ affineNegation W ≫ affineChart W) hc).symm

/-- Negation on the glued Weierstrass cubic over an arbitrary commutative base. -/
def negation : scheme W ⟶ scheme W :=
  pushout.desc (affineNegation W ≫ affineChart W) (infinityNegationGlued W) (negation_gluing W)

@[reassoc (attr := simp)] theorem affineChart_negation :
    affineChart W ≫ negation W = affineNegation W ≫ affineChart W :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem infinityChart_negation :
    infinityChart W ≫ negation W = infinityNegationGlued W :=
  pushout.inr_desc _ _ _

@[reassoc] theorem infinityNegationGlued_toBase :
    infinityNegationGlued W ≫ toBase W = chartToBase W true := by
  apply (negationInfinityCover W).hom_ext
  intro b
  cases b
  · change overlapInclusion W true ≫ (infinityNegationGlued W ≫ toBase W) =
      overlapInclusion W true ≫ chartToBase W true
    rw [overlap_infinityNegationGlued_assoc]
    simp only [affineChart_toBase, affineNegation_toBase]
    unfold overlapInclusion chartToBase
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact ((changeChart W true).commutes r).trans
      (IsScalarTower.algebraMap_apply R (Ring W true) (Overlap W true) r)
  · change Spec.map (CommRingCat.ofHom
        (algebraMap (Ring W true) (NegationNeighborhood W))) ≫
        (infinityNegationGlued W ≫ toBase W) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Ring W true) (NegationNeighborhood W))) ≫ chartToBase W true
    rw [neighborhood_infinityNegationGlued_assoc]
    simp only [infinityChart_toBase]
    unfold infinityNegationMorphism chartToBase
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact ((infinityNegationLocal W).commutes r).trans
      (IsScalarTower.algebraMap_apply R (Ring W true) (NegationNeighborhood W) r)

/-- The globally glued negation is a morphism over the coefficient base. -/
@[reassoc (attr := simp)] theorem negation_toBase :
    negation W ≫ toBase W = toBase W := by
  apply pushout.hom_ext
  · change affineChart W ≫ (negation W ≫ toBase W) = affineChart W ≫ toBase W
    simp
  · change infinityChart W ≫ (negation W ≫ toBase W) = infinityChart W ≫ toBase W
    simp only [infinityChart_negation_assoc, infinityChart_toBase, infinityNegationGlued_toBase]

end WeierstrassCurve.CubicCharts
