/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalCocycle
public import FLT.Mazur.SchemeIndependentFamilyLineCategory

/-!
# Canonical independent family data of a base line bundle

Ordinary member pullbacks carry canonical unequal pair identifications.
Their original diagonal and triple laws construct independent family data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SchemeIndependentCanonicalOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- A base line bundle supplies data on the original family members. -/
def canonicalObj (L : LineBundleCat X) : IndependentLineData 𝒰 where
  obj i := (lineBundlePullback (𝒰.f i)).obj L
  overlap ij := SchemeIndependentCanonicalOverlap.pair (𝒰.f ij.1) (𝒰.f ij.2) L.val
  diagonal i := by
    change SchemeGeometricDescent.Diagonal (𝒰.f i) ((pullback (𝒰.f i)).obj L.val)
      (SchemeIndependentCanonicalOverlap.pair (𝒰.f i) (𝒰.f i) L.val)
    simpa only [SchemeGeometricDescent.canonical, SchemePullbackOverlap.overlap,
      AffineIteratedPullbackSections.compositeIso_eq_comparison,
      SchemeIndependentCanonicalOverlap.pair, SchemeIndependentCanonicalOverlap.overlap] using
      (SchemeGeometricDescent.canonical (𝒰.f i) L.val).diagonal
  cocycle ijk := pair_cocycle (𝒰.f ijk.1.1) (𝒰.f ijk.1.2) (𝒰.f ijk.2) L.val

/-- Base maps intertwine the independently constructed pair overlaps. -/
lemma canonicalObj_mapCompatible {L K : LineBundleCat X} (a : L ⟶ K) :
    PairMapCompatible 𝒰 (canonicalObj 𝒰 L).overlap (canonicalObj 𝒰 K).overlap
      (fun i ↦ (pullback (𝒰.f i)).map a.hom) := by
  intro ij
  have hl := (SheafPullbackPathComparison.comparison
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2)) (𝒰.f ij.1) _ rfl).hom.naturality a.hom
  have hr := (SheafPullbackPathComparison.comparison
    (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2)) (𝒰.f ij.2)
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ 𝒰.f ij.1)
    Limits.pullback.condition.symm).inv.naturality a.hom
  dsimp only [Functor.comp_map] at hl hr
  dsimp only [canonicalObj, SchemeIndependentCanonicalOverlap.pair,
    SchemeIndependentCanonicalOverlap.overlap, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  rw [Category.assoc, ← hr, ← Category.assoc, ← hl, Category.assoc]

/-- Canonical independent descent is a functor on actual base line bundles. -/
def canonical : LineBundleCat X ⥤ IndependentLineData 𝒰 where
  obj := canonicalObj 𝒰
  map a := ⟨fun i ↦ (pullback (𝒰.f i)).map a.hom, canonicalObj_mapCompatible 𝒰 a⟩
  map_id _ := hom_ext (fun i ↦ (pullback (𝒰.f i)).map_id _)
  map_comp a b := hom_ext (fun i ↦ (pullback (𝒰.f i)).map_comp a.hom b.hom)

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
