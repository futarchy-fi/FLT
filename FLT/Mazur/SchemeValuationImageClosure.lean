/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSpecializationValuation
public import FLT.Mazur.NoetherianClosedImageGenerizations

/-!
# Valuative witnesses for closed image obstructions

The closure of a closed Noetherian source image is detected by valuation
squares with generic point in that source set. If the exact central fiber
misses the set, none of these squares extends to the ambient source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
namespace FLT.Mazur.SchemeSpecializationValuation
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every valuation square realizes a specialization of its actual generic source image. -/
theorem square_specializes (S : ValuativeCommSq f) :
    f (S.i₁ default) ⤳ S.i₂ (closedPoint S.R) := by
  have he := congrArg (fun t : Spec (.of S.K) ⟶ Y ↦ t default) S.commSq.w
  change f (S.i₁ default) =
    S.i₂ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) default) at he
  rw [he]
  exact (specializes_closedPoint _).map S.i₂.continuous

/-- Valuation squares detect the closure of a closed Noetherian source image. -/
theorem mem_closure_image_iff_square [NoetherianSpace X]
    {Z : Set X} (hZ : IsClosed Z) (y : Y) :
    y ∈ closure (f '' Z) ↔
      ∃ S : ValuativeCommSq f, S.i₁ default ∈ Z ∧ S.i₂ (closedPoint S.R) = y := by
  rw [NoetherianClosedImage.mem_closure_image_iff f f.continuous hZ]
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨S, hS, hcenter⟩ := exists_square f x y hxy
    exact ⟨S, by rwa [hS], hcenter⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.i₁ default, hS, square_specializes f S⟩

/-- Noetherian source image closures are exactly the possible valuative centers. -/
theorem mem_closure_range_iff_square [NoetherianSpace X] (y : Y) :
    y ∈ closure (Set.range f) ↔
      ∃ S : ValuativeCommSq f, S.i₂ (closedPoint S.R) = y := by
  simpa using mem_closure_image_iff_square f isClosed_univ y

/-- A lift carries a closed generic source condition to the closed point. -/
theorem lift_closedPoint_mem {Z : Set X} (hZ : IsClosed Z)
    (S : ValuativeCommSq f) (hS : S.i₁ default ∈ Z) (l : S.commSq.LiftStruct) :
    l.l (closedPoint S.R) ∈ Z := by
  have hsub : ({S.i₁ default} : Set X) ⊆ Z := Set.singleton_subset_iff.mpr hS
  exact closure_minimal hsub hZ (lift_specializes f S l).1.mem_closure

/-- An excluded exact fiber forces failure of every ambient extension of a bad generic point. -/
theorem no_lift_of_fiber_disjoint {Z : Set X} (hZ : IsClosed Z)
    (S : ValuativeCommSq f) (hS : S.i₁ default ∈ Z)
    (hf : ∀ x ∈ Z, f x ≠ S.i₂ (closedPoint S.R)) :
    ¬ S.commSq.HasLift := by
  intro hl
  obtain ⟨l⟩ := (CommSq.HasLift.iff S.commSq).mp hl
  exact hf _ (lift_closedPoint_mem f hZ S hS l) (lift_specializes f S l).2

end FLT.Mazur.SchemeSpecializationValuation
