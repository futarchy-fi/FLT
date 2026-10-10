/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyOverlapCover
public import FLT.Mazur.SchemeCoproductLineGluing
public import FLT.Mazur.ModuleSheafDisjointPullbackGluing

/-!
# Assembling independently supplied family overlap isomorphisms

The independently assembled source module has an actual isomorphism on the
total double overlap, recovering each supplied isomorphism on its original pair.
Diagonal and triple-cocycle laws are separate obligations.
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
variable (M : ∀ i, (𝒰.X i).Modules)

/-- Recovery of the first source module on an original pairwise overlap. -/
def pairLeftRecovery (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pullback (pairMap 𝒰 ij)).obj ((pullback (Limits.pullback.fst
      (projection 𝒰) (projection 𝒰))).obj (SchemeCoproductModuleGluing.assembled 𝒰.X M)) ≅
        (pullback (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))).obj (M ij.1) :=
  (pullbackComp (pairMap 𝒰 ij) (Limits.pullback.fst _ _)).app _ ≪≫
    (pullbackCongr (pairMap_fst 𝒰 ij)).app _ ≪≫
    (pullbackComp (Limits.pullback.fst _ _) (Limits.Sigma.ι 𝒰.X ij.1)).symm.app _ ≪≫
    (pullback (Limits.pullback.fst _ _)).mapIso
      (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.1)

/-- Recovery of the second source module on an original pairwise overlap. -/
def pairRightRecovery (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pullback (pairMap 𝒰 ij)).obj ((pullback (Limits.pullback.snd
      (projection 𝒰) (projection 𝒰))).obj (SchemeCoproductModuleGluing.assembled 𝒰.X M)) ≅
        (pullback (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))).obj (M ij.2) :=
  (pullbackComp (pairMap 𝒰 ij) (Limits.pullback.snd _ _)).app _ ≪≫
    (pullbackCongr (pairMap_snd 𝒰 ij)).app _ ≪≫
    (pullbackComp (Limits.pullback.snd _ _) (Limits.Sigma.ι 𝒰.X ij.2)).symm.app _ ≪≫
    (pullback (Limits.pullback.snd _ _)).mapIso
      (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.2)

/-- Independent isomorphisms on the original unequal fiber products. -/
abbrev PairIsomorphisms := ∀ ij : 𝒰.I₀ × 𝒰.I₀,
  (pullback (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))).obj (M ij.1) ≅
    (pullback (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))).obj (M ij.2)

/-- Every point of the total overlap lies in one original pair chart. -/
lemma pair_jointly_covers (x : (Limits.pullback (projection 𝒰) (projection 𝒰) : Scheme)) :
    ∃ ij, x ∈ Set.range (pairMap 𝒰 ij) := by
  have hx : x ∈ iSup (fun ij ↦ (pairMap 𝒰 ij).opensRange) := by
    rw [pairMap_covers]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- Assemble the supplied pairwise isomorphisms on the actual total double overlap. -/
def assembledOverlap (e : PairIsomorphisms 𝒰 M) :
    (pullback (Limits.pullback.fst (projection 𝒰) (projection 𝒰))).obj
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) ≅
    (pullback (Limits.pullback.snd (projection 𝒰) (projection 𝒰))).obj
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) :=
  ModuleSheafDisjointPullbackGluing.glueIso (pair 𝒰) (pairMap 𝒰)
    (pairMap_disjoint 𝒰) (pair_jointly_covers 𝒰)
    (fun ij ↦ pairLeftRecovery 𝒰 M ij ≪≫ e ij ≪≫ (pairRightRecovery 𝒰 M ij).symm)

/-- The assembled overlap recovers precisely the independently supplied pair isomorphism. -/
lemma assembledOverlap_recovery (e : PairIsomorphisms 𝒰 M) (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pullback (pairMap 𝒰 ij)).map (assembledOverlap 𝒰 M e).hom ≫
        (pairRightRecovery 𝒰 M ij).hom = (pairLeftRecovery 𝒰 M ij).hom ≫ (e ij).hom := by
  unfold assembledOverlap
  rw [ModuleSheafDisjointPullbackGluing.pullback_glueIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.SchemeFppfFamily
