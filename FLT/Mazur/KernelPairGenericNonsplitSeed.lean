/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSeedGenericImage
public import FLT.Mazur.KernelPairGenericBranchInverses

/-!
# Effective generic neighborhoods from partial nonsplit seed certificates

Generic seed kernel image certificates and original source orbit coverage
construct inverse neighborhoods in the full original kernel. No complete
seed kernel model or equality of seed coordinates is required. The resulting
effective open belongs to the unchanged coefficient target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w)
  [Etale p.left] [Etale q.left] [Mono (pullback.lift p.left q.left h)]
  [IrreducibleSpace T] (a : Z ⟶ A.left) [Etale a] [Etale (a ≫ w)] [Nonempty Z]
local notation "m" => pullback.lift p.left q.left h
local notation "C" => (pullback (a ≫ w) (a ≫ w) : Scheme)
variable
  (hs : ∀ z : (pullback (a ≫ w) (a ≫ w) : Scheme),
    (pullback.fst (a ≫ w) (a ≫ w) ≫ (a ≫ w)) z = genericPoint T →
      z ∈ Set.range (SchemeRelationSeedKernelTransport.seedComparison w h a))
  (hc : ∀ x : A.left, w x = genericPoint T →
    ∃ z : Z, RelativeRelationOrbit.Related p q x (a z))

include e hs hc

/-- Partial nonsplit seed certificates construct actual inverses at every generic kernel point. -/
theorem generic_inverse_of_nonsplit_seed :
    ∀ x : (pullback w w : Scheme), (pullback.fst w w ≫ w) x = genericPoint T →
      x ∈ MonomorphismOpenImage.locus m :=
  generic_inverse_of_source_branch p.left q.left w h a
    (SchemeRelationSeedKernelTransport.generic_image e w h a hs hc)

variable [IsNoetherian A.left] [IsNoetherian T]
  [LocallyOfFinitePresentation w] [QuasiCompact w]

/-- The constructed inverses spread to a nonempty effective open of the original target. -/
theorem targetOpen_nonempty_of_nonsplit_seed :
    (targetOpen p.left q.left w h : Set T).Nonempty :=
  targetOpen_nonempty_of_source_branch p.left q.left w h a
    (SchemeRelationSeedKernelTransport.generic_image e w h a hs hc)

/-- The original seed reaches the fppf region of the full original source restriction. -/
theorem fppfLocus_nonempty_of_nonsplit_seed :
    (SchemeFppfTargetOpen.locus (projection p.left q.left w h) :
      Set (targetOpen p.left q.left w h).toScheme).Nonempty :=
  fppfLocus_nonempty_of_source_branch p.left q.left w h a
    (SchemeRelationSeedKernelTransport.generic_image e w h a hs hc)

end FLT.Mazur.KernelPairEffectiveOpen
