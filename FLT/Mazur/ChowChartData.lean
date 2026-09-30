/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseChartImmersion

/-!
# Chow chart data over a field

For a separated finite-type scheme over a field, `chartData` constructs a
finite affine open cover and actual projective immersions over that field.
Every chart contains every component generic point, so the common open is
dense even for a reducible source. The common-open maps retain the original
structure morphism. The construction also allows the empty scheme.

This packages the chart input to Stacks 0200. Scheme-theoretic closure and
the resulting modification belong to the subsequent graph construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace FLT.Mazur.Chow

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The finite affine chart data, including the projective immersions and their
compatibility with the given structure morphism. -/
structure ChartData (f : X ⟶ Spec (.of k)) where
  /-- The finite set of charts. -/
  Index : Type u
  /-- A chosen finite enumeration of the charts. -/
  indexFintype : Fintype Index
  /-- The affine open subsets of the original scheme. -/
  opens : Index → X.Opens
  /-- Every chart is affine. -/
  affine : ∀ i, IsAffineOpen (opens i)
  /-- Empty charts are unnecessary, including for an empty source. -/
  nonempty : ∀ i, (opens i : Set X).Nonempty
  /-- The charts cover the source. -/
  covers : iSup opens = ⊤
  /-- Each chart contains every component generic point. -/
  containsGenerics : ∀ i, genericPoints X ⊆ opens i
  /-- The dimension of the projective space for each chart. -/
  dimension : Index → ℕ
  /-- The actual morphisms to projective space. -/
  immersion : ∀ i, (opens i).toScheme ⟶ ProjectiveSpace.space k (Fin (dimension i + 1))
  /-- The chart morphisms are immersions. -/
  isImmersion : ∀ i, IsImmersion (immersion i)
  /-- Every immersion is over the given field spectrum. -/
  over_base : ∀ i, immersion i ≫ ProjectiveSpace.baseProjection k
    (Fin (dimension i + 1)) = (opens i).ι ≫ f
  /-- The restricted structure morphisms retain finite type and separatedness. -/
  properties : ∀ i, LocallyOfFiniteType ((opens i).ι ≫ f) ∧
    QuasiCompact ((opens i).ι ≫ f) ∧ IsSeparated ((opens i).ι ≫ f)

namespace ChartData

variable {f : X ⟶ Spec (.of k)} (D : ChartData f)

instance finiteIndex : Fintype D.Index := D.indexFintype

instance chartIsImmersion (i : D.Index) : IsImmersion (D.immersion i) := D.isImmersion i

/-- The actual intersection open, with no additional choice. -/
def common : X.Opens := commonOpen D.opens

/-- All component generic points lie in the common open. -/
lemma common_contains_generics : genericPoints X ⊆ D.common :=
  commonOpen_contains_generics D.opens D.containsGenerics

/-- The common open is dense in the original scheme. -/
lemma common_dense : Dense (D.common : Set X) :=
  commonOpen_dense_of_generics D.opens D.containsGenerics

/-- The common open maps to each projective factor through its affine chart. -/
def commonToProjective (i : D.Index) :
    D.common.toScheme ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)) :=
  commonToChart D.opens i ≫ D.immersion i

instance commonToProjective_isImmersion (i : D.Index) :
    IsImmersion (D.commonToProjective i) := by
  let _chartImmersion := D.isImmersion i
  let _commonImmersion : IsImmersion (commonToChart D.opens i) := inferInstance
  exact IsImmersion.comp (commonToChart D.opens i) (D.immersion i)

/-- Every projective component has the original common-open structure map. -/
@[reassoc (attr := simp)]
lemma commonToProjective_baseProjection (i : D.Index) :
    D.commonToProjective i ≫ ProjectiveSpace.baseProjection k
      (Fin (D.dimension i + 1)) = D.common.ι ≫ f := by
  simp only [commonToProjective, Category.assoc, D.over_base, commonToChart_ι_assoc,
    common]

end ChartData

/-- Construct all chart data from the separated finite-type structure map.
No cover, projective immersion, or comparison is part of the input. -/
def chartData (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] : ChartData f :=
  Classical.choice <| by
    obtain ⟨ι, hι, U, n, j, hU, hne, hcover, hg, _, _, hj, hbase, hprops⟩ :=
      exists_dense_affine_projective_chart_cover_over_field f
    exact ⟨⟨ι, hι, U, hU, hne, hcover, hg, n, j, hj, hbase, hprops⟩⟩

end FLT.Mazur.Chow
