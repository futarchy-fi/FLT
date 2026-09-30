/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineCover
public import FLT.Mazur.ChowGenericNeighborhoods

/-!
# A finite affine cover with dense common open

For a scheme with Noetherian underlying space, we construct a finite affine
cover whose every chart contains every component generic point. Its common
open is therefore dense, even when the scheme is reducible. This is the
topological cover step of Stacks 0200 using the Noetherian case of 01ZX.

The cover is an output. The empty scheme is allowed, with an empty index set.
For a separated finite-type morphism to a Noetherian base, the charts retain
the original structure map, finite type, and separatedness. The common-open
inclusions are the maps already defined in `ChowAffineCover`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace FLT.Mazur.Chow

variable {X S : Scheme.{u}}

/-- A finite intersection of opens containing all component generic points
still contains all of them. -/
lemma commonOpen_contains_generics {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hg : ∀ i, genericPoints X ⊆ U i) : genericPoints X ⊆ commonOpen U := by
  intro η hη
  rw [commonOpen, Opens.coe_iInf]
  exact Set.mem_iInter.mpr fun i ↦ hg i hη

/-- Keeping every component generic point makes the common open dense;
irreducibility of the entire scheme is unnecessary. -/
lemma commonOpen_dense_of_generics {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hg : ∀ i, genericPoints X ⊆ U i) : Dense (commonOpen U : Set X) := by
  apply Dense.mono (commonOpen_contains_generics U hg)
  exact dense_iff_closure_eq.mpr genericPoints.closure

/-- Construct a finite affine cover by nonempty charts, all containing every
component generic point. Its actual common open contains those points and is
dense. The Noetherian assumption is only on the underlying topology. -/
theorem exists_finite_affine_cover_all_generics (X : Scheme.{u}) [NoetherianSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧ iSup U = ⊤ ∧
      (∀ i, genericPoints X ⊆ U i) ∧ genericPoints X ⊆ commonOpen U ∧
      Dense (commonOpen U : Set X) := by
  classical
  choose V hV hx hg using fun x : X ↦ exists_affine_mem_all_generics x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let U : t → X.Opens := fun i ↦ V i
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  have hgenerics (i : t) : genericPoints X ⊆ U i := hg i
  exact ⟨t, inferInstance, U, fun i ↦ hV i, fun i ↦ ⟨i, hx i⟩, hcover,
    hgenerics, commonOpen_contains_generics U hgenerics,
    commonOpen_dense_of_generics U hgenerics⟩

/-- The affine-cover input to Chow's construction for a separated finite-type
morphism over a Noetherian base, including reducible sources. Every chart has
the original structure morphism restricted to it. -/
theorem exists_noetherian_dense_affine_cover (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧ iSup U = ⊤ ∧
      (∀ i, genericPoints X ⊆ U i) ∧ genericPoints X ⊆ commonOpen U ∧
      Dense (commonOpen U : Set X) ∧
      (∀ i, LocallyOfFiniteType ((U i).ι ≫ f) ∧ QuasiCompact ((U i).ι ≫ f) ∧
        IsSeparated ((U i).ι ≫ f)) := by
  let _sourceNoetherian := source_isNoetherian f
  obtain ⟨ι, hι, U, hU, hne, hcover, hg, hcommon, hdense⟩ :=
    exists_finite_affine_cover_all_generics X
  exact ⟨ι, hι, U, hU, hne, hcover, hg, hcommon, hdense,
    fun i ↦ affine_chart_properties f (U i)⟩

end FLT.Mazur.Chow
