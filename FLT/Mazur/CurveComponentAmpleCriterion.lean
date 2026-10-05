/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IrreducibleComponentAmple
public import FLT.Mazur.CurveAmpleDegree
public import Mathlib.AlgebraicGeometry.Artinian

/-!
# Positive component degree and ampleness

Stacks 0B5Y: on a proper scheme of dimension at most one, ampleness is
equivalent to positive degree on each one-dimensional reduced irreducible
component. Zero-dimensional components impose no degree condition.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

namespace FLT.Mazur.FCurve
open CoherentDevissage

/-- A line on a zero-dimensional integral Noetherian scheme is ample. -/
theorem ampleLineBundle_of_integral_dim_zero {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) {L : X.Modules}
    (hL : LocallyFreeRankOne L) : AmpleLineBundle L := by
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero hd
  have : Subsingleton X := ⟨fun x y ↦
    DiscreteTopology.isDiscrete.subsingleton_of_isPreirreducible
      PreirreducibleSpace.isPreirreducible_univ (Set.mem_univ x) (Set.mem_univ y)⟩
  obtain ⟨e⟩ := hL.trivial_of_subsingleton (genericPoint X)
  exact ampleLineBundle_structure_of_affine.of_iso e

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] {L : X.Modules}

include f in
/-- Stacks 0B5Y, with degree tested only on the one-dimensional components. -/
theorem ampleLineBundle_iff_positive_component_degree
    (hd : topologicalKrullDim X ≤ 1) (hL : LocallyFreeRankOne L) :
    AmpleLineBundle L ↔ ∀ Z : Closeds X, (Z : Set X) ∈ irreducibleComponents X →
      topologicalKrullDim (reducedClosedSubscheme Z) = 1 →
      0 < curveSheafDegree (reducedClosedSubschemeι Z ≫ f)
        ((pullback (reducedClosedSubschemeι Z)).obj L) := by
  rw [ampleLineBundle_iff_on_irreducibleComponents f hL]
  constructor
  · intro h Z hZ hdim
    let : IsIntegral (reducedClosedSubscheme Z) := reducedClosedSubscheme_isIntegral Z hZ.1
    exact (h Z hZ).curveSheafDegree_pos (reducedClosedSubschemeι Z ≫ f) hdim
  · intro h Z hZ
    let : IsIntegral (reducedClosedSubscheme Z) := reducedClosedSubscheme_isIntegral Z hZ.1
    have := Chow.source_isNoetherian (reducedClosedSubschemeι Z ≫ f)
    by_cases hdim : topologicalKrullDim (reducedClosedSubscheme Z) = 1
    · exact (ampleLineBundle_iff_curveSheafDegree_pos (reducedClosedSubschemeι Z ≫ f)
        hdim (hL.pullback _)).mpr (h Z hZ hdim)
    · have he := (reducedClosedSubschemeι Z).isClosedEmbedding.isEmbedding.isInducing
      have hle : topologicalKrullDim (reducedClosedSubscheme Z) ≤ 1 :=
        he.topologicalKrullDim_le.trans hd
      have hz : topologicalKrullDim (reducedClosedSubscheme Z) ≤ 0 :=
        Order.le_of_lt_succ (lt_of_le_of_ne hle hdim)
      exact ampleLineBundle_of_integral_dim_zero hz (hL.pullback _)

end FLT.Mazur.FCurve
