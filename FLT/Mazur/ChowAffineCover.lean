/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# The affine-cover part of Chow's construction

Stacks 0200 starts with a separated finite-type morphism to a Noetherian base.
It chooses finitely many affine opens containing every generic point, and keeps
their common dense open. We construct a finite cover by nonempty affine opens
and prove density of its common open when the source is irreducible. The
simultaneous generic-point neighborhoods for a reducible source and projective
immersions of the charts are separate inputs still to be constructed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace FLT.Mazur.Chow

variable {X S : Scheme.{u}}

/-- A compact scheme has a finite affine cover with no empty charts. -/
theorem exists_finite_nonempty_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧ iSup U = ⊤ := by
  classical
  have hlocal (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x)
      (by trivial)
    exact ⟨U, hU, hx⟩
  choose V hV hx using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, inferInstance, fun i ↦ V i, fun i ↦ hV i,
    fun i ↦ ⟨i, hx i⟩, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩

/-- The common open is the finite intersection, with its actual open subscheme. -/
def commonOpen {ι : Type u} (U : ι → X.Opens) : X.Opens := ⨅ i, U i

/-- The common open maps into every chart. -/
def commonToChart {ι : Type u} (U : ι → X.Opens) (i : ι) :
    (commonOpen U).toScheme ⟶ (U i).toScheme :=
  X.homOfLE (iInf_le U i)

instance commonToChart_isOpenImmersion {ι : Type u} (U : ι → X.Opens) (i : ι) :
    IsOpenImmersion (commonToChart U i) := by
  dsimp [commonToChart]
  infer_instance

/-- The chart inclusions preserve the map of the common open into the source. -/
@[reassoc (attr := simp)]
lemma commonToChart_ι {ι : Type u} (U : ι → X.Opens) (i : ι) :
    commonToChart U i ≫ (U i).ι = (commonOpen U).ι := by
  exact X.homOfLE_ι (iInf_le U i)

/-- For an irreducible scheme, all nonempty opens contain its generic point. -/
lemma genericPoint_mem_open [IrreducibleSpace X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact (genericPoint_specializes x).mem_open U.isOpen hx

/-- The finite intersection retains the generic point and is therefore dense. -/
lemma commonOpen_dense [IrreducibleSpace X] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, (U i : Set X).Nonempty) :
    Dense (commonOpen U : Set X) := by
  apply (commonOpen U).isOpen.dense
  refine ⟨genericPoint X, ?_⟩
  rw [commonOpen, Opens.coe_iInf]
  exact Set.mem_iInter.mpr fun i ↦ genericPoint_mem_open (U i) (hU i)

/-- Finite type over a Noetherian base gives the Noetherian source used in 0200. -/
lemma source_isNoetherian (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  let _sourceLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
  let _sourceCompact := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- Each affine chart retains finite type and separatedness over the original base. -/
lemma affine_chart_properties (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (U : X.Opens) :
    LocallyOfFiniteType (U.ι ≫ f) ∧ QuasiCompact (U.ι ≫ f) ∧
      IsSeparated (U.ι ≫ f) := by
  let _sourceNoetherian := source_isNoetherian f
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The irreducible case of the finite-type affine-cover input to Chow's lemma.
The cover and its common dense open are conclusions, not chosen input data. -/
theorem exists_irreducible_affine_cover (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IrreducibleSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      (∀ i, LocallyOfFiniteType ((U i).ι ≫ f) ∧ QuasiCompact ((U i).ι ≫ f) ∧
        IsSeparated ((U i).ι ≫ f)) ∧ Dense (commonOpen U : Set X) := by
  let _sourceNoetherian := source_isNoetherian f
  obtain ⟨ι, hι, U, hU, hne, hcover⟩ := exists_finite_nonempty_affine_cover X
  exact ⟨ι, hι, U, hU, hcover, fun i ↦ affine_chart_properties f (U i),
    commonOpen_dense U hne⟩

end FLT.Mazur.Chow
