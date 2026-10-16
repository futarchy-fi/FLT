/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameScalarExtension

/-!
# Completeness survives and descends along field extension

The original coordinate images pull back exactly. Hence a complete frame stays
complete after arbitrary scalar extension, and completeness is also reflected.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [IsSeparated E.hom]
  (I : Type) [Fintype I] {K L : Type} [Field K] [Field L]
  {b : Spec (.of K) ⟶ S} (t : Over.mk b ⟶ distinctScheme E I)
  (g : Spec (.of L) ⟶ Spec (.of K))

/-- Each original coordinate image pulls back exactly, with no discarded points. -/
theorem scalarFrame_coordinate_range (i : I) :
    Set.range (geometricCoordinate E I (scalarFrame E I t g) i) =
      scalarFiberMap E g ⁻¹' Set.range (geometricCoordinate E I t i) := by
  have H := scalarFrame_coordinate_isPullback E I t g i
  rw [← H.isoPullback_hom_snd]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr H.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_snd]

variable [Etale E.hom]

/-- A complete original frame remains complete over every field extension. -/
theorem scalarFrame_complete
    (ht : Function.Bijective (fun i ↦ geometricCoordinate E I t i default)) :
    Function.Bijective (fun i ↦ geometricCoordinate E I (scalarFrame E I t g) i default) := by
  refine ⟨geometricCoordinate_point_injective E I _, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := ht.2 (scalarFiberMap E g x)
  have hx : x ∈ Set.range (geometricCoordinate E I (scalarFrame E I t g) i) := by
    rw [scalarFrame_coordinate_range]
    exact ⟨default, hi⟩
  obtain ⟨y, hy⟩ := hx
  exact ⟨i, (congrArg (geometricCoordinate E I (scalarFrame E I t g) i)
    (Subsingleton.elim default y)).trans hy⟩

omit [IsSeparated E.hom] [Etale E.hom] in
/-- Field extension is surjective on the entire original fibers. -/
theorem scalarFiberMap_surjective : Function.Surjective (scalarFiberMap E (b := b) g) := by
  have H := scalarFiberMap_isPullback E (b := b) g
  rw [← Set.range_eq_univ, ← H.isoPullback_hom_fst]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr H.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_fst]
  have hg : Set.range g = Set.univ :=
    Set.range_eq_univ.mpr (Function.surjective_to_subsingleton g)
  rw [hg, Set.preimage_univ]

/-- Completeness can also be checked after any field extension. -/
theorem scalarFrame_complete_iff :
    Function.Bijective (fun i ↦ geometricCoordinate E I (scalarFrame E I t g) i default) ↔
      Function.Bijective (fun i ↦ geometricCoordinate E I t i default) := by
  refine ⟨fun ht ↦ ⟨geometricCoordinate_point_injective E I t, ?_⟩,
    scalarFrame_complete E I t g⟩
  intro x
  obtain ⟨y, hy⟩ := scalarFiberMap_surjective E g x
  obtain ⟨i, hi⟩ := ht.2 y
  dsimp only at hi
  refine ⟨i, ?_⟩
  have h := congrArg (fun f ↦ f default) (scalarFrame_geometric E I t g i)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hi, hy] at h
  exact (congrArg (geometricCoordinate E I t i)
    (Subsingleton.elim default (g default))).trans h.symm

end FLT.Mazur.RelativeOrderedTuples
