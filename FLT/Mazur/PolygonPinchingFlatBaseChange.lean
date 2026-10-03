/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackLocalPushout
public import FLT.Mazur.PolygonPinchingAffineBaseChange

/-!
# Flat base change of the specified polygon pinching pushout

The normalization remains a surjective schematic epimorphism. Affine-base
pushouts therefore glue over the parameter scheme's affine open cover.
The conclusion applies to any supplied pinching cocone and includes n = 1.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.PolygonPinchingFlatBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type u) [Field K] (n : ℕ) [NeZero n]
instance atlas_reduced : IsReduced (PolygonAtlas.polygon K n).left := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact PolygonNormalizationDominant.oneGon_reduced K
  · exact PolygonNormalizationDominant.cyclic_reduced K (n + 2) (by omega)
instance normalization_surjective : Surjective (PolygonAtlas.normalization K n).left :=
  ⟨PolygonNormalizationFinite.normalization_surjective K n⟩
instance normalization_dominant :
    IsSchemeTheoreticallyDominant (PolygonAtlas.normalization K n).left := .of_isDominant _
variable {T : Scheme.{u}} (g : T ⟶ Spec (.of K)) [Flat g]
instance pullback_finite : IsFinite ((Over.pullback g).map (PolygonAtlas.normalization K n)).left :=
  MorphismProperty.of_isPullback
    (OverPullbackLocalPushout.map_isPullback g (PolygonAtlas.normalization K n)).flip inferInstance
instance pullback_surjective :
    Surjective ((Over.pullback g).map (PolygonAtlas.normalization K n)).left :=
  MorphismProperty.of_isPullback
    (OverPullbackLocalPushout.map_isPullback g (PolygonAtlas.normalization K n)).flip inferInstance
instance pullback_dominant :
    IsSchemeTheoreticallyDominant ((Over.pullback g).map (PolygonAtlas.normalization K n)).left :=
  PolygonNormalizationDominant.dominant_of_isPullback
    (OverPullbackLocalPushout.map_isPullback g (PolygonAtlas.normalization K n))
variable (hn : 0 < n)
theorem atlas_isPushout :
    IsPushout ((Over.pullback g).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback g).map (PolygonPinching.toNodes K n))
      ((Over.pullback g).map (PolygonAtlas.normalization K n))
      ((Over.pullback g).map (PolygonAtlas.nodes K n)) := by
  apply PinchingPushoutCriterion.isPushout_of_existsUnique
  · rw [← Functor.map_comp, ← Functor.map_comp, PolygonAtlas.cocone]
  · intro Y f q w
    apply OverPullbackLocalPushout.exists_desc
      ((Over.pullback g).map (PolygonAtlas.normalization K n))
      ((Over.pullback g).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback g).map (PolygonPinching.toNodes K n))
      ((Over.pullback g).map (PolygonAtlas.nodes K n)) T.affineCover _ f q w
    intro i
    let α := Over.pullbackComp (T.affineCover.f i) g
    exact (PolygonPinchingAffineBaseChange.affine_pullback K n hn
      (T.affineCover.f i ≫ g) (PolygonAtlas.normalization K n) (PolygonAtlas.nodes K n)
      (PolygonAtlas.isPushout K n hn)).of_iso
        (α.app _) (α.app _) (α.app _) (α.app _)
        (α.hom.naturality _) (α.hom.naturality _) (α.hom.naturality _) (α.hom.naturality _)
theorem pinching_pullback {C : Over (Spec (.of K))}
    (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
    (h : IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q) :
    IsPushout ((Over.pullback g).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback g).map (PolygonPinching.toNodes K n))
      ((Over.pullback g).map p) ((Over.pullback g).map q) := by
  apply (atlas_isPushout K n g hn).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Over.pullback g).mapIso (PolygonPinching.polygonIso K n hn p q h))
  · simp
  · simp
  · simp [← Functor.map_comp]
  · simp [← Functor.map_comp]
end FLT.Mazur.PolygonPinchingFlatBaseChange
