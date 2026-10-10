/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalIsoGluing
public import FLT.Mazur.SchemeIndependentCanonicalUnitFrames

/-!
# Descending compatible line bundle frames

Specified local trivializations agreeing on original pair overlaps descend to
a global trivialization, with their exact pullback-and-unit recovery equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard FCurve SchemeIndependentCanonicalOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (L : LineBundleCat X)
  (a : ∀ i, (pullback (𝒰.f i)).obj L.val ≅ structureModule (𝒰.X i))
  (ha : ∀ i j, (SchemeIndependentCanonicalOverlap.pair (𝒰.f i) (𝒰.f j) L.val).hom ≫
      (pullback (Limits.pullback.snd (𝒰.f i) (𝒰.f j))).map (a j).hom ≫
        (modulePullbackUnitIso (Limits.pullback.snd (𝒰.f i) (𝒰.f j))).hom =
    (pullback (Limits.pullback.fst (𝒰.f i) (𝒰.f j))).map (a i).hom ≫
      (modulePullbackUnitIso (Limits.pullback.fst (𝒰.f i) (𝒰.f j))).hom)

include ha in
/-- Original local frames give a compatible map to the canonical structure-module datum. -/
lemma frames_mapCompatible :
    PairMapCompatible 𝒰 (canonicalObj 𝒰 L).overlap
      (canonicalObj 𝒰 ⟨structureModule X, structureModule_locallyFreeRankOne⟩).overlap
      (fun i ↦ (a i ≪≫ (modulePullbackUnitIso (𝒰.f i)).symm).hom) := by
  intro ij
  apply (cancel_mono ((pullback (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))).map
    (modulePullbackUnitIso (𝒰.f ij.2)).hom ≫
      (modulePullbackUnitIso (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))).hom)).mp
  dsimp only [canonicalObj, Iso.trans_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [pair_unit]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact ha ij.1 ij.2

/-- The global trivialization obtained from the specified original frames. -/
def glueFrame : L.val ≅ structureModule X :=
  glueIso 𝒰 (L := L) (K := ⟨structureModule X, structureModule_locallyFreeRankOne⟩)
    (fun i ↦ a i ≪≫ (modulePullbackUnitIso (𝒰.f i)).symm)
    (frames_mapCompatible 𝒰 L a ha)

/-- Pullback of the global trivialization recovers the specified original local frame. -/
lemma glueFrame_member (i : 𝒰.I₀) :
    (pullback (𝒰.f i)).map (glueFrame 𝒰 L a ha).hom ≫
      (modulePullbackUnitIso (𝒰.f i)).hom = (a i).hom := by
  rw [glueFrame, glueIso_member]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
