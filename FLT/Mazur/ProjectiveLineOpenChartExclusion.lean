/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineTopology

/-!
# Open exclusions from any nonempty chart of a projective line

A nonempty open chart is dense, so its image detects whether the complete
projective image meets a given open subscheme of the target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
universe u
variable (K : Type u) [Field K]

/-- Every nonempty open chart of the projective line has dense image. -/
theorem openChart_denseRange {V : Scheme.{u}} [Nonempty V]
    (j : V ⟶ scheme K) [IsOpenImmersion j] : DenseRange j :=
  j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _

/-- A target open missing a nonempty source chart misses the complete projective image. -/
theorem map_range_open_disjoint_of_chart {V X U : Scheme.{u}} [Nonempty V]
    (j : V ⟶ scheme K) [IsOpenImmersion j]
    (f : scheme K ⟶ X) (g : U ⟶ X) [IsOpenImmersion g]
    (h : Disjoint (Set.range (j ≫ f)) (Set.range g)) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  have ho : IsOpen (f ⁻¹' Set.range g) :=
    g.isOpenEmbedding.isOpen_range.preimage f.continuous
  obtain ⟨y, hy⟩ := (openChart_denseRange K j).exists_mem_open ho ⟨x, hx⟩
  exact Set.disjoint_left.mp h ⟨y, rfl⟩ hy

end FLT.Mazur.ProjectiveLine
