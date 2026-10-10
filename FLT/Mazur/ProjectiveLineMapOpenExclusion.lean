/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineTopology

/-!
# Open exclusions extend from an affine chart to a complete projective line

Density rules out an isolated extra intersection at the omitted endpoint.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
universe u
variable (K : Type u) [Field K]

/-- The entire left affine chart is dense in the projective line. -/
theorem left_denseRange : DenseRange (left K) :=
  (left K).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _

/-- An open chart missing the full affine image also misses the complete projective image. -/
theorem map_range_open_disjoint_of_left {X U : Scheme.{u}}
    (f : scheme K ⟶ X) (g : U ⟶ X) [IsOpenImmersion g]
    (h : Disjoint (Set.range (left K ≫ f)) (Set.range g)) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  have ho : IsOpen (f ⁻¹' Set.range g) :=
    g.isOpenEmbedding.isOpen_range.preimage f.continuous
  obtain ⟨y, hy⟩ := (left_denseRange K).exists_mem_open ho ⟨x, hx⟩
  exact Set.disjoint_left.mp h ⟨y, rfl⟩ hy

end FLT.Mazur.ProjectiveLine
