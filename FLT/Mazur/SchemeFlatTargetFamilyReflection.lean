/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatFamilyReflection
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Flatness descends through a jointly surjective flat target family

Pulling back the family gives a jointly surjective flat source family.
This permits completion and generic localization to detect flatness even
when the original morphism is not affine.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFlatTargetFamilyReflection
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A flat target family detects flatness through its actual pullback projections. -/
theorem flat_of_family {ι : Type*} (Y : ι → Scheme.{u}) (p : ∀ i, Y i ⟶ S)
    [∀ i, Flat (p i)] (hp : ∀ s : S, ∃ i, ∃ y : Y i, p i y = s)
    (h : ∀ i, Flat (pullback.snd f (p i))) : Flat f := by
  apply SchemeFlatFamilyReflection.flat_of_family f
    (fun i ↦ pullback f (p i)) (fun i ↦ pullback.fst f (p i))
  · intro x
    obtain ⟨i, y, hy⟩ := hp (f x)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := p i)
      x y hy.symm
    exact ⟨i, z, hz⟩
  · intro i
    let _ := h i
    rw [pullback.condition]
    infer_instance

/-- Two flat maps whose ranges cover the target suffice, without a finiteness hypothesis. -/
theorem flat_of_pair {Y Z : Scheme.{u}} (p : Y ⟶ S) (q : Z ⟶ S)
    [Flat p] [Flat q] (hpq : ∀ s : S, s ∈ Set.range p ∨ s ∈ Set.range q)
    [Flat (pullback.snd f p)] [Flat (pullback.snd f q)] : Flat f := by
  let V : Bool → Scheme.{u} := fun b ↦ if b then Y else Z
  let v : ∀ b, V b ⟶ S := fun b ↦ by
    cases b
    · exact q
    · exact p
  let _ (b : Bool) : Flat (v b) := by cases b <;> dsimp [v] <;> infer_instance
  apply flat_of_family f V v
  · intro s
    obtain ⟨y, hy⟩ | ⟨z, hz⟩ := hpq s
    · exact ⟨true, y, hy⟩
    · exact ⟨false, z, hz⟩
  · intro b
    cases b <;> dsimp [v] <;> infer_instance

end FLT.Mazur.SchemeFlatTargetFamilyReflection
