/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCoproductModuleEquivalence
public import FLT.Mazur.ModuleLineBundleOpenCover
public import FLT.Mazur.SchemeLineBundleCategory

/-!
# Assembling independent line bundles on scheme coproducts

The constructed module assembly is locally free of rank one whenever all its
original components are. Recovery preserves the supplied line bundles and maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeCoproductModuleGluing
open FCurve SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] assembled
variable {ι : Type u} (X : ι → Scheme.{u})

/-- The concrete assembly of independent line bundles is a line bundle. -/
theorem assembled_locallyFreeRankOne (M : ∀ i, (X i).Modules)
    (hM : ∀ i, LocallyFreeRankOne (M i)) : LocallyFreeRankOne (assembled X M) :=
  LocallyFreeRankOne.of_openPullbackCover X (Limits.Sigma.ι X) (jointly_covers X)
    (fun i ↦ (hM i).of_iso (recovery X M i).symm)

/-- Assemble independently supplied line bundles on all coproduct members. -/
def assembleLine : (∀ i, LineBundleCat (X i)) ⥤ LineBundleCat (∐ X) where
  obj L := ⟨assembled X (fun i ↦ (L i).val),
    assembled_locallyFreeRankOne X _ (fun i ↦ (L i).property)⟩
  map f := InducedCategory.homMk (map X (fun i ↦ (f i).hom))
  map_id _ := InducedCategory.hom_ext (map_id X)
  map_comp f g := InducedCategory.hom_ext
    (map_comp X (fun i ↦ (f i).hom) (fun i ↦ (g i).hom))

/-- Decompose a line bundle using the actual coproduct inclusions. -/
def decomposeLine : LineBundleCat (∐ X) ⥤ (∀ i, LineBundleCat (X i)) where
  obj L i := (lineBundlePullback (Limits.Sigma.ι X i)).obj L
  map f i := (lineBundlePullback (Limits.Sigma.ι X i)).map f

/-- The chosen assembly retains the original line bundle on every member. -/
def lineRecovery (L : ∀ i, LineBundleCat (X i)) (i : ι) :
    (lineBundlePullback (Limits.Sigma.ι X i)).obj ((assembleLine X).obj L) ≅ L i :=
  InducedCategory.isoMk (recovery X (fun j ↦ (L j).val) i)

/-- All independent line bundles and all their maps are recovered naturally. -/
def lineMemberRecovery : assembleLine X ⋙ decomposeLine X ≅ 𝟭 _ :=
  NatIso.ofComponents (fun L ↦ Pi.isoMk (lineRecovery X L)) (fun f ↦ by
    funext i
    apply InducedCategory.hom_ext
    exact map_recovery X (fun j ↦ (f j).hom) i)

instance decomposeLine_faithful : (decomposeLine X).Faithful where
  map_injective h := by
    apply InducedCategory.hom_ext
    apply (decompose X).map_injective
    funext i
    have hi := congrArg (fun f ↦ f.hom) (congrFun h i)
    exact hi

instance decomposeLine_full : (decomposeLine X).Full where
  map_surjective f := by
    let g := (decompose X).preimage (fun i ↦ (f i).hom)
    refine ⟨InducedCategory.homMk g, ?_⟩
    funext i
    apply InducedCategory.hom_ext
    exact congrFun ((decompose X).map_preimage (fun j ↦ (f j).hom)) i

instance decomposeLine_essSurj : (decomposeLine X).EssSurj where
  mem_essImage L := ⟨(assembleLine X).obj L, ⟨Pi.isoMk (lineRecovery X L)⟩⟩

instance decomposeLine_isEquivalence : (decomposeLine X).IsEquivalence where

/-- Line bundles on a coproduct are equivalent to independently supplied line bundles. -/
def lineEquivalence : LineBundleCat (∐ X) ≌ (∀ i, LineBundleCat (X i)) :=
  (decomposeLine X).asEquivalence

end FLT.Mazur.SchemeCoproductModuleGluing
