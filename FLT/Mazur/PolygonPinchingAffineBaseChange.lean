/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicPinchingProduct
public import FLT.Mazur.OneGonPinchingProduct
public import FLT.Mazur.PolygonCoconeComparison
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Pinching pushouts over an arbitrary affine scheme

Combine both polygon sizes, transport to any supplied pinching cocone,
and recover the coefficient algebra from the affine parameter morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.PolygonPinchingAffineBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
variable (n : ℕ) [NeZero n] (hn : 0 < n)
open PinchingChartBaseChange
theorem atlas_isPushout :
    IsPushout ((Over.pullback (parameter K S)).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback (parameter K S)).map (PolygonPinching.toNodes K n))
      ((Over.pullback (parameter K S)).map (PolygonAtlas.normalization K n))
      ((Over.pullback (parameter K S)).map (PolygonAtlas.nodes K n)) := by
  by_cases h : 2 ≤ n
  · apply (CyclicPinchingProduct.isPushout K S n h hn).of_iso'
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Over.pullback (parameter K S)).mapIso (PolygonAtlas.cyclicIso K n h))
    · simp
    · simp
    · simp [← Functor.map_comp]
    · simp [← Functor.map_comp]
  · have he : n = 1 := by omega
    subst n
    apply (OneGonPinchingProduct.isPushout K S hn).of_iso'
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Over.pullback (parameter K S)).mapIso (PolygonAtlas.oneGonIso K))
    · simp
    · simp
    · simp [← Functor.map_comp]
    · simp [← Functor.map_comp]
theorem pinching_pullback {C : Over (Spec (.of K))}
    (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
    (h : IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q) :
    IsPushout ((Over.pullback (parameter K S)).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback (parameter K S)).map (PolygonPinching.toNodes K n))
      ((Over.pullback (parameter K S)).map p) ((Over.pullback (parameter K S)).map q) := by
  apply (atlas_isPushout K S n hn).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Over.pullback (parameter K S)).mapIso (PolygonPinching.polygonIso K n hn p q h))
  · simp
  · simp
  · simp [← Functor.map_comp]
  · simp [← Functor.map_comp]
omit [Algebra K S] in
theorem spec_pullback (g : Spec (.of S) ⟶ Spec (.of K))
    {C : Over (Spec (.of K))}
    (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
    (h : IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q) :
    IsPushout ((Over.pullback g).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback g).map (PolygonPinching.toNodes K n))
      ((Over.pullback g).map p) ((Over.pullback g).map q) := by
  have hp := @pinching_pullback K S _ _ (Spec.preimage g).hom.toAlgebra n _ hn _ p q h
  have he : @parameter K S _ _ (Spec.preimage g).hom.toAlgebra = g := Spec.map_preimage g
  rw [he] at hp
  exact hp
theorem affine_pullback {T : Scheme.{u}} [IsAffine T] (g : T ⟶ Spec (.of K))
    {C : Over (Spec (.of K))}
    (p : PolygonPinching.components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
    (h : IsPushout (PolygonPinching.toComponents K n hn) (PolygonPinching.toNodes K n) p q) :
    IsPushout ((Over.pullback g).map (PolygonPinching.toComponents K n hn))
      ((Over.pullback g).map (PolygonPinching.toNodes K n))
      ((Over.pullback g).map p) ((Over.pullback g).map q) := by
  let e := T.isoSpec
  let : (Over.pullback e.inv).IsEquivalence :=
    (Over.mapPullbackAdj e.inv).isEquivalence_right_of_isEquivalence_left
  apply IsPushout.of_map_of_faithful (Over.pullback e.inv)
  let α := Over.pullbackComp e.inv g
  exact (spec_pullback K Γ(T, ⊤) n hn (e.inv ≫ g) p q h).of_iso
    (α.app _) (α.app _) (α.app _) (α.app _)
    (α.hom.naturality _) (α.hom.naturality _) (α.hom.naturality _) (α.hom.naturality _)
end FLT.Mazur.PolygonPinchingAffineBaseChange
