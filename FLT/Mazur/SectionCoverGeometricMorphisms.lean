/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointSectionCoverCartesian

/-!
# Complete section covers classify whole geometric morphisms

An open section cover captures every field-valued lift as a morphism,
including residue-field embeddings. Disjointness makes the sheet unique;
this is stronger than enumeration of the underlying topological points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SectionCoverGeometricMorphisms
universe u
variable {E U : Scheme.{u}} (p : E ⟶ U) {ι : Type*}
  (a : ι → (U ⟶ E)) [∀ i, IsOpenImmersion (a i)]
  (ha : ∀ i, a i ≫ p = 𝟙 U) (hc : ∀ x : E, ∃ i, a i (p x) = x)
  {K : Type u} [Field K] (b : Spec (.of K) ⟶ U)

include ha hc in
/-- Every field-valued lift factors through a section as an entire scheme morphism. -/
theorem exists_sheet (w : Spec (.of K) ⟶ E) (hw : w ≫ p = b) :
    ∃ i, w = b ≫ a i := by
  obtain ⟨i, hi⟩ := hc (w default)
  have hr : Set.range w ⊆ Set.range (a i) := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (default : Spec (.of K))]
    exact ⟨p (w default), hi⟩
  let v := IsOpenImmersion.lift (a i) w hr
  have hv : v ≫ a i = w := IsOpenImmersion.lift_fac _ _ _
  have hvb : v = b := by
    calc
      v = v ≫ a i ≫ p := by rw [ha, Category.comp_id]
      _ = b := by rw [← Category.assoc, hv, hw]
  exact ⟨i, hv.symm.trans (congrArg (fun z ↦ z ≫ a i) hvb)⟩

include ha hc in
/-- Pairwise disjoint sheets classify each field-valued lift uniquely. -/
theorem existsUnique_sheet
    (hd : Pairwise (fun i j ↦ Disjoint (Set.range (a i)) (Set.range (a j))))
    (w : Spec (.of K) ⟶ E) (hw : w ≫ p = b) :
    ∃! i, w = b ≫ a i := by
  obtain ⟨i, hi⟩ := exists_sheet p a ha hc b w hw
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  by_contra hji
  have h := congrArg (fun z : Spec (.of K) ⟶ E ↦ z default) (hj.symm.trans hi)
  exact Set.disjoint_left.mp (hd hji) ⟨b default, rfl⟩ ⟨b default, h.symm⟩

include ha hc in
/-- Any property of entire geometric lifts can be checked on the complete section family. -/
theorem forall_lifts_iff (P : (Spec (.of K) ⟶ E) → Prop) :
    (∀ w, w ≫ p = b → P w) ↔ ∀ i, P (b ≫ a i) := by
  constructor
  · intro h i
    apply h
    rw [Category.assoc, ha, Category.comp_id]
  · intro h w hw
    obtain ⟨i, rfl⟩ := exists_sheet p a ha hc b w hw
    exact h i

end FLT.Mazur.SectionCoverGeometricMorphisms
