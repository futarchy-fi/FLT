/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityOutputTransition
public import FLT.Mazur.WeierstrassInfinityAdditionScheme
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The concrete infinity intersection is the scheme fiber product

The localization square is a ring pushout and hence a scheme pullback. Thus
output-transition compatibility holds on the actual intersection of the two
addition domains, rather than merely on a chosen common restriction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (t : Fin 3)

/-- The concrete localized ring gives the actual scheme intersection of the two domains. -/
theorem infinityProjective_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (infinityProjectiveRestriction W t).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityProjectivePolynomial W t).toRingHom))
      (infinityAdditionInclusion W) (projectiveAdditionInclusion W 1 1 t) := by
  have : IsLocalization
      ((Submonoid.powers (chartProductAdditionCoordinates W 1 1 t)).map
        (infinityAdditionRestriction W).toRingHom)
      (InfinityProjectiveOverlap W t) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization (infinityAdditionRestriction W).toRingHom
    (infinityProjectivePolynomial W t).toRingHom
    (congrArg AlgHom.toRingHom (infinityProjective_inputs W t))
    (Submonoid.powers (chartProductAdditionCoordinates W 1 1 t))

/-- The explicit isomorphism from the localized spectrum to the domain fiber product. -/
def infinityProjectivePullbackIso :
    Spec (CommRingCat.of (InfinityProjectiveOverlap W t)) ≅
      pullback (infinityAdditionInclusion W) (projectiveAdditionInclusion W 1 1 t) :=
  (infinityProjective_isPullback W t).isoPullback

/-- The first projection is the actual infinity-domain restriction. -/
@[reassoc] theorem infinityProjectivePullbackIso_fst :
    (infinityProjectivePullbackIso W t).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (infinityProjectiveRestriction W t).toRingHom) :=
  (infinityProjective_isPullback W t).isoPullback_hom_fst

/-- The second projection is the actual polynomial-domain restriction. -/
@[reassoc] theorem infinityProjectivePullbackIso_snd :
    (infinityProjectivePullbackIso W t).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (infinityProjectivePolynomial W t).toRingHom) :=
  (infinityProjective_isPullback W t).isoPullback_hom_snd

/-- The polynomial restriction is an open immersion into its original domain. -/
instance infinityProjectivePolynomial_isOpenImmersion :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (infinityProjectivePolynomial W t).toRingHom)) := by
  rw [← infinityProjectivePullbackIso_snd]
  infer_instance

/-- On the scheme intersection, addition agrees after the integral output-chart transition. -/
theorem infinityProjective_output_spec :
    Spec.map (CommRingCat.ofHom (infinityProjectivePolynomial W t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 t).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityIntersectionOutputLift W t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 t).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityIntersectionOutput_compatibility W t)

end FLT.Mazur.WeierstrassIntegralChart
