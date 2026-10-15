/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Data.Set.Card

/-!
# Simultaneous geometric sections through every point of a finite étale fiber

One separably closed test supplies actual morphisms through every original
fiber point. Their evaluations enumerate that fiber without repetition.
These are original topological branches; their number need not be the degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EtaleFiniteFiberGeometricSections
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)

/-- Every finite original fiber has a complete family of lifts on the same geometric test. -/
theorem exists_enumeration (hf : (f ⁻¹' {b default}).Finite) :
    ∃ a : Fin (f ⁻¹' {b default}).ncard → (Spec (.of K) ⟶ X),
      (∀ i, a i ≫ f = b) ∧ Function.Injective (fun i ↦ a i default) ∧
      Set.range (fun i ↦ a i default) = f ⁻¹' {b default} := by
  let _ := hf.fintype
  let e : Fin (f ⁻¹' {b default}).ncard ≃ (f ⁻¹' {b default}) :=
    (Finite.equivFin (f ⁻¹' {b default})).symm
  have h (i : Fin (f ⁻¹' {b default}).ncard) :=
    Scheme.exists_fac_of_etale_of_isSepClosed f b (e i).val (e i).property
  choose a ha hp using h
  refine ⟨a, ha, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (hp i).symm.trans (hij.trans (hp j))
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      change f (a i default) = b default
      rw [hp i]
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, (hp i).trans (congrArg Subtype.val hi)⟩

/-- Finite-fiber sections are distinct as whole morphisms, not just chosen representatives. -/
theorem exists_distinct_lifts (hf : (f ⁻¹' {b default}).Finite) :
    ∃ a : Fin (f ⁻¹' {b default}).ncard → (Spec (.of K) ⟶ X),
      Function.Injective a ∧ (∀ i, a i ≫ f = b) ∧
      Set.range (fun i ↦ a i default) = f ⁻¹' {b default} := by
  obtain ⟨a, ha, hi, hr⟩ := exists_enumeration f b hf
  exact ⟨a, fun i j h ↦ hi (congrArg (fun z : Spec (.of K) ⟶ X ↦ z default) h),
    ha, hr⟩

end FLT.Mazur.EtaleFiniteFiberGeometricSections
