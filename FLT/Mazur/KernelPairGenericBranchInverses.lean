/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationEtaleBranchPropagation
public import FLT.Mazur.KernelPairGenericEffectiveOpen
public import FLT.Mazur.KernelPairEffectiveEtaleBranch

/-!
# Constructing generic inverse neighborhoods from one original source branch

Point coverage of the entire generic kernel, together with a single nonempty
branch etale over both source and target, constructs the missing inverse
neighborhoods. Propagation through the full original relation replaces global
unramifiedness and the previously required pointwise etale kernel lifts.
The target is allowed to be nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T Z : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T)
  (h : p ≫ w = q ≫ w) [Etale p] [Etale q] [Mono (pullback.lift p q h)]
  [IrreducibleSpace T] (a : Z ⟶ A) [Etale a] [Etale (a ≫ w)] [Nonempty Z]
local notation "m" => pullback.lift p q h
local notation "v" => pullback.fst w w ≫ w

include a

/-- Generic point coverage and one source branch construct actual inverses at all kernel points. -/
theorem generic_inverse_of_source_branch
    (hg : ∀ x : (pullback w w : Scheme), v x = genericPoint T → x ∈ Set.range m) :
    ∀ x : (pullback w w : Scheme), v x = genericPoint T →
      x ∈ MonomorphismOpenImage.locus m := by
  obtain ⟨z, hz⟩ := SchemeRelationEtaleBranchPropagation.exists_generic_seed w a
  let b := SchemeRelationEtaleBranchPropagation.branch p q a
  let _ : Etale (b ≫ w) :=
    SchemeRelationEtaleBranchPropagation.branch_target_etale p q w h a
  have hcover : ∀ y : A, w y = genericPoint T → y ∈ Set.range b := by
    intro y hy
    apply SchemeRelationEtaleBranchPropagation.fiber_subset_branch p q w h a z
    · intro k hk
      exact hg k (hk.trans hz)
    · exact hy.trans hz.symm
  intro x hx
  apply KernelPairEtaleSourceBranch.mem_inverse_of_image p q w h b x (hg x hx)
  apply hcover
  have he := congrArg (fun g ↦ g x) (pullback.condition (f := w) (g := w))
  exact he.symm.trans hx

variable [IsNoetherian A] [IsNoetherian T] [LocallyOfFinitePresentation w] [QuasiCompact w]

/-- The constructed inverse neighborhoods spread over a nonempty unchanged target open. -/
theorem targetOpen_nonempty_of_source_branch
    (hg : ∀ x : (pullback w w : Scheme), v x = genericPoint T → x ∈ Set.range m) :
    (targetOpen p q w h : Set T).Nonempty :=
  (targetOpen_nonempty_iff_genericFiber p q w h).mpr
    (generic_inverse_of_source_branch p q w h a hg)

/-- The original seed then reaches a represented whole-source fppf neighborhood. -/
theorem fppfLocus_nonempty_of_source_branch
    (hg : ∀ x : (pullback w w : Scheme), v x = genericPoint T → x ∈ Set.range m) :
    (SchemeFppfTargetOpen.locus (projection p q w h) :
      Set (targetOpen p q w h).toScheme).Nonempty :=
  fppfLocus_nonempty_of_etale_branch p q w h a
    (targetOpen_nonempty_of_source_branch p q w h a hg)

end FLT.Mazur.KernelPairEffectiveOpen
