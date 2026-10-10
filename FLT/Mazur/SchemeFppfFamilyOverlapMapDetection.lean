/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyOverlapMapAssembly

/-!
# Detecting original pair-map compatibility from assembly

The recovery squares detect as well as preserve pair-map compatibility.
Thus assembled geometric maps have exactly the original pair equations.
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

/-- The assembled compatibility equation detects every original pair equation. -/
lemma pairMapCompatible_of_assembled (e : PairIsomorphisms 𝒰 M)
    (e' : PairIsomorphisms 𝒰 N) (f : ∀ i, M i ⟶ N i)
    (h : (assembledOverlap 𝒰 M e).hom ≫
      (pullback (Limits.pullback.snd (projection 𝒰) (projection 𝒰))).map
        (SchemeCoproductModuleGluing.map 𝒰.X f) =
      (pullback (Limits.pullback.fst (projection 𝒰) (projection 𝒰))).map
        (SchemeCoproductModuleGluing.map 𝒰.X f) ≫ (assembledOverlap 𝒰 N e').hom) :
    PairMapCompatible 𝒰 e e' f := by
  intro ij
  have hh := congrArg ((pullback (pairMap 𝒰 ij)).map) h
  simp only [Functor.map_comp] at hh
  apply (cancel_epi (pairLeftRecovery 𝒰 M ij).hom).mp
  rw [← Category.assoc, ← assembledOverlap_recovery, Category.assoc,
    ← pairRightRecovery_map, ← Category.assoc, hh, Category.assoc,
    assembledOverlap_recovery, ← Category.assoc, pairLeftRecovery_map]
  exact Category.assoc _ _ _

end FLT.Mazur.SchemeFppfFamily
