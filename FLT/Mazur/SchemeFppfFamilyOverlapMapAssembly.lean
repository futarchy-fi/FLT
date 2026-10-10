/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyPairMapRecovery

/-!
# Assembling maps compatible with original family overlaps

Compatibility is checked on the original pairs. Their jointly surjective
open charts detect compatibility of the actual assembled source map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable {M N : ∀ i, (𝒰.X i).Modules}

/-- Original pair equations for independently supplied component maps. -/
def PairMapCompatible (e : PairIsomorphisms 𝒰 M) (e' : PairIsomorphisms 𝒰 N)
    (f : ∀ i, M i ⟶ N i) : Prop := ∀ ij : 𝒰.I₀ × 𝒰.I₀,
  (e ij).hom ≫ (pullback (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))).map (f ij.2) =
    (pullback (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))).map (f ij.1) ≫ (e' ij).hom

/-- Original pair compatibility implies compatibility of the actual assembled overlaps. -/
lemma assembledOverlap_map (e : PairIsomorphisms 𝒰 M) (e' : PairIsomorphisms 𝒰 N)
    (f : ∀ i, M i ⟶ N i) (hf : PairMapCompatible 𝒰 e e' f) :
    (assembledOverlap 𝒰 M e).hom ≫
        (pullback (Limits.pullback.snd (projection 𝒰) (projection 𝒰))).map
          (SchemeCoproductModuleGluing.map 𝒰.X f) =
      (pullback (Limits.pullback.fst (projection 𝒰) (projection 𝒰))).map
        (SchemeCoproductModuleGluing.map 𝒰.X f) ≫ (assembledOverlap 𝒰 N e').hom := by
  apply ModuleSheafOpenImmersionGluing.hom_ext (pair 𝒰) (pairMap 𝒰)
    (pair_jointly_covers 𝒰)
  intro ij
  apply (cancel_mono (pairRightRecovery 𝒰 N ij).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [pairRightRecovery_map, ← Category.assoc, assembledOverlap_recovery]
  rw [Category.assoc, hf ij, ← Category.assoc]
  rw [← pairLeftRecovery_map, Category.assoc, assembledOverlap_recovery]

end FLT.Mazur.SchemeFppfFamily
