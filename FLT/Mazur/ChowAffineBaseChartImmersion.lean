/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineEmbedding
public import FLT.Mazur.ChowDenseAffineCover
public import FLT.Mazur.ProjectiveAffineChartEmbedding
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Projective immersions of the dense affine charts over an affine base

A finite-type affine scheme over `Spec R` embeds into polynomial affine space
as a closed subscheme and then into the zeroth projective chart as an open
subscheme. The resulting immersion commutes with the given map to `Spec R`.
Applying it to the constructed dense affine cover supplies projective
immersions for every chart, including when the original scheme is reducible.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace FLT.Mazur.Chow

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- An affine scheme locally of finite type over an affine base has a genuine
projective immersion over that base. -/
theorem exists_projective_chart_immersion [IsAffine X]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (j : X ⟶ ProjectiveSpace.space R (Fin (n + 1))),
      IsImmersion j ∧ j ≫ ProjectiveSpace.baseProjection R (Fin (n + 1)) = f := by
  obtain ⟨n, j, hj, hbase⟩ := exists_closed_polynomial_embedding f
  let _closed := hj
  refine ⟨n, j ≫ ProjectiveSpace.affineChartEmbedding R n, inferInstance, ?_⟩
  rw [Category.assoc, ProjectiveSpace.affineChartEmbedding_baseProjection, hbase]

/-- Every affine open of a finite-type scheme over `Spec R` has a projective
immersion whose base map is the original map restricted to the open. -/
theorem affine_open_projective_immersion (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (j : U.toScheme ⟶ ProjectiveSpace.space R (Fin (n + 1))),
      IsImmersion j ∧ j ≫ ProjectiveSpace.baseProjection R (Fin (n + 1)) = U.ι ≫ f := by
  let _affine : IsAffine U.toScheme := hU
  exact exists_projective_chart_immersion (U.ι ≫ f)

/-- The finite dense affine cover admits projective immersions on all charts,
with every base identity retained. No cover or immersion is an input witness. -/
theorem exists_dense_affine_projective_chart_cover [IsNoetherianRing R]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens) (n : ι → ℕ)
      (j : ∀ i, (U i).toScheme ⟶ ProjectiveSpace.space R (Fin (n i + 1))),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧ iSup U = ⊤ ∧
      (∀ i, genericPoints X ⊆ U i) ∧ genericPoints X ⊆ commonOpen U ∧
      Dense (commonOpen U : Set X) ∧ (∀ i, IsImmersion (j i)) ∧
      (∀ i, j i ≫ ProjectiveSpace.baseProjection R (Fin (n i + 1)) = (U i).ι ≫ f) ∧
      (∀ i, LocallyOfFiniteType ((U i).ι ≫ f) ∧ QuasiCompact ((U i).ι ≫ f) ∧
        IsSeparated ((U i).ι ≫ f)) := by
  obtain ⟨ι, hι, U, hU, hne, hcover, hg, hcommon, hdense, hprops⟩ :=
    exists_noetherian_dense_affine_cover f
  choose n j hj hbase using fun i ↦ affine_open_projective_immersion f (U i) (hU i)
  exact ⟨ι, hι, U, n, j, hU, hne, hcover, hg, hcommon, hdense, hj, hbase, hprops⟩

/-- In particular, the chart-embedding step applies over the spectrum of a field. -/
theorem exists_dense_affine_projective_chart_cover_over_field
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens) (n : ι → ℕ)
      (j : ∀ i, (U i).toScheme ⟶ ProjectiveSpace.space k (Fin (n i + 1))),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧ iSup U = ⊤ ∧
      (∀ i, genericPoints X ⊆ U i) ∧ genericPoints X ⊆ commonOpen U ∧
      Dense (commonOpen U : Set X) ∧ (∀ i, IsImmersion (j i)) ∧
      (∀ i, j i ≫ ProjectiveSpace.baseProjection k (Fin (n i + 1)) = (U i).ι ≫ f) ∧
      (∀ i, LocallyOfFiniteType ((U i).ι ≫ f) ∧ QuasiCompact ((U i).ι ≫ f) ∧
        IsSeparated ((U i).ι ≫ f)) :=
  exists_dense_affine_projective_chart_cover f

end FLT.Mazur.Chow
