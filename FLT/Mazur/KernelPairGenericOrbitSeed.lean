/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedImage
public import FLT.Mazur.KernelPairGenericBranchInverses

/-!
# Effective generic neighborhoods from one monic orbit seed

For a seed open over the coefficient target, coverage of the generic SOURCE
fiber by its original relation saturation constructs all generic kernel
inverses. This replaces the independent whole-kernel point coverage premise.
The target may be nonreduced and the source need not be integral.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w)
  [Etale p.left] [Etale q.left] [Mono (pullback.lift p.left q.left h)]
  [IrreducibleSpace T] (a : Z ⟶ A.left) [Etale a] [IsOpenImmersion (a ≫ w)]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "m" => pullback.lift p.left q.left h
local notation "v" => pullback.fst w w ≫ w

include e

/-- A monic seed turns generic source orbit coverage into full scheme kernel inverse patches. -/
theorem generic_inverse_of_orbit_seed
    (hc : ∀ x : A.left, w x = genericPoint T → x ∈ Set.range b) :
    ∀ x : (pullback w w : Scheme), v x = genericPoint T →
      x ∈ MonomorphismOpenImage.locus m := by
  let _ : Etale (b ≫ w) :=
    SchemeRelationEtaleBranchPropagation.branch_target_etale p.left q.left w h a
  intro x hx
  apply KernelPairEtaleSourceBranch.mem_inverse_of_image p.left q.left w h b x
  · exact SchemeRelationMonicSeedKernel.fiber_subset_image e w h a (genericPoint T) hc x hx
  · apply hc
    have he := congrArg (fun g ↦ g x) (pullback.condition (f := w) (g := w))
    exact he.symm.trans hx

variable [IsNoetherian A.left] [IsNoetherian T]
  [LocallyOfFinitePresentation w] [QuasiCompact w]

/-- Source orbit coverage spreads the constructed inverses over an unchanged target open. -/
theorem targetOpen_nonempty_of_orbit_seed
    (hc : ∀ x : A.left, w x = genericPoint T → x ∈ Set.range b) :
    (targetOpen p.left q.left w h : Set T).Nonempty :=
  (targetOpen_nonempty_iff_genericFiber p.left q.left w h).mpr
    (generic_inverse_of_orbit_seed e w h a hc)

/-- A nonempty seed then constructs a represented region of the complete original source. -/
theorem fppfLocus_nonempty_of_orbit_seed [Nonempty Z]
    (hc : ∀ x : A.left, w x = genericPoint T → x ∈ Set.range b) :
    (SchemeFppfTargetOpen.locus (projection p.left q.left w h) :
      Set (targetOpen p.left q.left w h).toScheme).Nonempty :=
  fppfLocus_nonempty_of_etale_branch p.left q.left w h a
    (targetOpen_nonempty_of_orbit_seed e w h a hc)

end FLT.Mazur.KernelPairEffectiveOpen
