/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicProductNormalization
public import FLT.Mazur.OneGonProductNormalization
public import FLT.Mazur.PolygonNormalizationFinite
public import FLT.Mazur.SchematicDescentGluing
/-!
# Schematic epimorphisms from polygon normalization

The original polygon is reduced, so its finite surjective normalization is
schematically dominant. Flat base change gives the cancellation used in gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.PolygonNormalizationDominant
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

instance oneGon_reduced : IsReduced (OneGonGluing.scheme K) := by
  let U := PolygonProductAtlas.oneGonCover K
  have : ∀ b, IsReduced (U.X b) := by
    intro b
    cases b
    · change IsReduced (Spec (.of (PolygonNodePresentation.B (R := K))))
      infer_instance
    · change IsReduced (Spec (.of (LaurentPolynomial K)))
      infer_instance
  exact IsReduced.of_openCover _ U

instance cyclic_reduced (n : ℕ) (hn : 2 ≤ n) :
    IsReduced (PolygonCyclicAtlas.scheme K n hn) := by
  let U := PolygonProductAtlas.cyclicCover K n hn
  have : ∀ i, IsReduced (U.X i) := by
    intro i
    change IsReduced (Spec (.of (PolygonNodeEqualizer.A (R := K))))
    have : _root_.IsReduced (PolygonNodeEqualizer.A (R := K)) :=
      isReduced_of_injective (PolygonNodeEqualizer.inclusion (R := K)).toRingHom
        PolygonNodeEqualizer.inclusion_injective
    infer_instance
  exact IsReduced.of_openCover _ U

instance oneGon_surjective : Surjective (OneGonNormalization.normalization K) :=
  ⟨OneGonNormalizationFinite.normalization_surjective K⟩
instance cyclic_surjective (n : ℕ) (hn : 2 ≤ n) :
    Surjective (PolygonCyclicNormalizationPullback.normalization K n hn) :=
  ⟨PolygonCyclicNormalizationFinite.normalization_surjective K n hn⟩
instance oneGon_dominant :
    IsSchemeTheoreticallyDominant (OneGonNormalization.normalization K) :=
  .of_isDominant _
instance cyclic_dominant (n : ℕ) (hn : 2 ≤ n) :
    IsSchemeTheoreticallyDominant (PolygonCyclicNormalizationPullback.normalization K n hn) :=
  .of_isDominant _

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X}

theorem dominant_of_isPullback (h : IsPullback f' g' g f) [Flat g]
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] : IsSchemeTheoreticallyDominant f' := by
  rw [← h.isoPullback_hom_fst]
  infer_instance

instance oneGonProduct_finite : IsFinite (OneGonProductNormalization.normalizationProduct K S) :=
  MorphismProperty.of_isPullback
    (OneGonProductNormalization.normalizationProduct_isPullback K S).flip inferInstance
instance oneGonProduct_surjective :
    Surjective (OneGonProductNormalization.normalizationProduct K S) :=
  MorphismProperty.of_isPullback
    (OneGonProductNormalization.normalizationProduct_isPullback K S).flip inferInstance
instance oneGonProduct_dominant :
    IsSchemeTheoreticallyDominant (OneGonProductNormalization.normalizationProduct K S) :=
  dominant_of_isPullback (OneGonProductNormalization.normalizationProduct_isPullback K S)
instance oneGonProduct_epi : Epi (OneGonProductNormalization.normalizationProduct K S) :=
  SurjectiveDominantEpi.epi _

instance cyclicProduct_finite (n : ℕ) (hn : 2 ≤ n) :
    IsFinite (CyclicProductNormalization.normalizationProduct K S n hn) :=
  MorphismProperty.of_isPullback
    (CyclicProductNormalization.normalizationProduct_isPullback K S n hn).flip inferInstance
instance cyclicProduct_surjective (n : ℕ) (hn : 2 ≤ n) :
    Surjective (CyclicProductNormalization.normalizationProduct K S n hn) :=
  MorphismProperty.of_isPullback
    (CyclicProductNormalization.normalizationProduct_isPullback K S n hn).flip inferInstance
instance cyclicProduct_dominant (n : ℕ) (hn : 2 ≤ n) :
    IsSchemeTheoreticallyDominant (CyclicProductNormalization.normalizationProduct K S n hn) :=
  dominant_of_isPullback (CyclicProductNormalization.normalizationProduct_isPullback K S n hn)
instance cyclicProduct_epi (n : ℕ) (hn : 2 ≤ n) :
    Epi (CyclicProductNormalization.normalizationProduct K S n hn) := SurjectiveDominantEpi.epi _
end FLT.Mazur.PolygonNormalizationDominant
