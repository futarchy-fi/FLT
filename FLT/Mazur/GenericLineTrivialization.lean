/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointGenericNeighborhoods
public import FLT.Mazur.DisjointRestrictionIso
public import FLT.Mazur.DivisorInvertibleSheaf

/-!
# Trivializing a line at all component generic points

Disjoint generic neighborhoods allow the local trivializations of an arbitrary
line to glue over one dense open. This does not require integrality or even
reducedness, and includes the empty scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{0}} [NoetherianSpace X]

/-- A smaller open inherits a chosen trivialization against the ambient structure sheaf. -/
def smallerLineTrivialization {L : X.Modules} {V W : X.Opens} (h : V ≤ W)
    (e : L.restrict W.ι ≅ structureModule W.toScheme) :
    L.restrict V.ι ≅ (structureModule X).restrict V.ι :=
  DisjointRestrictionIso.shrink (M := L) (N := structureModule X) h
    (e ≪≫ (restrictUnitIso W.ι).symm)

/-- Local line trivializations can be chosen on disjoint generic neighborhoods. -/
theorem exists_disjoint_generic_line_trivializations {L : X.Modules}
    (hL : LocallyFreeRankOne L) :
    ∃ V : genericPoints X → X.Opens,
      Pairwise (fun η ξ ↦ Disjoint (V η) (V ξ)) ∧
      genericPoints X ⊆ (iSup V : X.Opens) ∧
      Dense (↑(iSup V : X.Opens) : Set X) ∧
      ∀ η, Nonempty (L.restrict (V η).ι ≅ (structureModule X).restrict (V η).ι) := by
  choose W hW e using fun η : genericPoints X ↦ hL η.val
  obtain ⟨V, hVW, _, hd, hg, hDense⟩ :=
    DisjointGenericNeighborhoods.exists_disjoint_refinement W hW
  exact ⟨V, hd, hg, hDense, fun η ↦
    ⟨smallerLineTrivialization (hVW η) (e η).some⟩⟩

/-- The unit restriction comparison, with both endpoints expressed as structure modules. -/
def lineStructureRestrictionIso (U : X.Opens) :
    (structureModule X).restrict U.ι ≅ structureModule U.toScheme :=
  restrictUnitIso U.ι

/-- Gluing the disjoint local trivializations produces a trivialization over the union. -/
def lineUnionTrivialization {L : X.Modules} {ι : Type} (V : ι → X.Opens)
    (hd : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (e : ∀ i, L.restrict (V i).ι ≅ (structureModule X).restrict (V i).ι) :
    L.restrict (iSup V).ι ≅ structureModule (iSup V).toScheme :=
  (DisjointRestrictionIso.glue (M := L) (N := structureModule X) V hd e).trans
    (lineStructureRestrictionIso (iSup V))

omit [NoetherianSpace X] in
/-- Package a disjoint generic trivializing family as one dense-open trivialization. -/
theorem line_trivialization_of_disjoint_generics {L : X.Modules} {ι : Type}
    (V : ι → X.Opens) (hd : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hg : genericPoints X ⊆ (iSup V : X.Opens))
    (e : ∀ i, Nonempty (L.restrict (V i).ι ≅ (structureModule X).restrict (V i).ι)) :
    ∃ U : X.Opens, genericPoints X ⊆ U ∧ Dense (U : Set X) ∧
      Nonempty (L.restrict U.ι ≅ structureModule U.toScheme) :=
  ⟨iSup V, hg, (dense_iff_closure_eq.mpr genericPoints.closure).mono hg,
    ⟨lineUnionTrivialization V hd (fun i ↦ (e i).some)⟩⟩

omit [NoetherianSpace X] in
/-- Existential disjoint families also give a single trivializing open. -/
theorem line_trivialization_of_exists_disjoint {L : X.Modules} {ι : Type}
    (h : ∃ V : ι → X.Opens,
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      genericPoints X ⊆ (iSup V : X.Opens) ∧
      Dense (↑(iSup V : X.Opens) : Set X) ∧
      ∀ i, Nonempty (L.restrict (V i).ι ≅ (structureModule X).restrict (V i).ι)) :
    ∃ U : X.Opens, genericPoints X ⊆ U ∧ Dense (U : Set X) ∧
      Nonempty (L.restrict U.ι ≅ structureModule U.toScheme) := by
  obtain ⟨V, hd, hg, _, e⟩ := h
  exact line_trivialization_of_disjoint_generics (L := L) V hd hg e

/-- An arbitrary line is trivial on one open containing every component generic point. -/
theorem exists_line_trivialization_all_generics {L : X.Modules}
    (hL : LocallyFreeRankOne L) :
    ∃ U : X.Opens, genericPoints X ⊆ U ∧ Dense (U : Set X) ∧
      Nonempty (L.restrict U.ι ≅ structureModule U.toScheme) :=
  line_trivialization_of_exists_disjoint (L := L) (ι := genericPoints X)
    (exists_disjoint_generic_line_trivializations hL)

end FLT.Mazur.FCurve
