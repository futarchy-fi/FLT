/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite full endpoint sources give finite comparison tests

For a triangle D → T → A, the comparison test over B → T is a closed
subscheme of the full endpoint test over B → A when T → A is separated.
Thus finiteness of the entire endpoint pullback constructs finiteness of the
comparison pullback, on arbitrary, possibly nonreduced coefficient schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteEndpointComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D T A B : Scheme.{0}} (c : D ⟶ T) (x : T ⟶ A) (b : B ⟶ T)

/-- A finite source restriction preserves finiteness of the full coefficient pullback. -/
theorem finite_pullback_precomp {D' : Scheme.{0}} (i : D' ⟶ D) (p : D ⟶ A)
    (a : B ⟶ A) [IsFinite i] [IsFinite (pullback.snd p a)] :
    IsFinite (pullback.snd (i ≫ p) a) := by
  rw [← pullbackRightPullbackFstIso_inv_snd_snd p a i]
  infer_instance

/-- The full comparison test is finite whenever its full endpoint test is finite. -/
theorem finite_pullback_of_finite_endpoint [IsSeparated x]
    [IsFinite (pullback.snd (c ≫ x) (b ≫ x))] :
    IsFinite (pullback.snd c b) := by
  have hf : IsFinite (pullback.mapDesc c b x ≫ pullback.snd (c ≫ x) (b ≫ x)) :=
    inferInstance
  simpa only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id] using hf

/-- A monic comparison cuts out a full closed subscheme of every such coefficient test. -/
theorem closedImmersion_pullback_of_finite_endpoint [IsSeparated x] [Mono c]
    [IsFinite (pullback.snd (c ≫ x) (b ≫ x))] :
    IsClosedImmersion (pullback.snd c b) := by
  let _ := finite_pullback_of_finite_endpoint c x b
  exact (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- The entire pulled-back comparison image is closed, without a finite branch choice. -/
theorem isClosed_preimage_range_of_finite_endpoint [IsSeparated x]
    [IsFinite (pullback.snd (c ≫ x) (b ≫ x))] : IsClosed (b ⁻¹' Set.range c) := by
  let _ := finite_pullback_of_finite_endpoint c x b
  rw [← Scheme.Pullback.range_snd]
  exact (pullback.snd c b).isClosedMap.isClosed_range

/-- Actual comparison-image membership survives every specialization in the coefficient test. -/
theorem mem_range_of_specializes_of_finite_endpoint [IsSeparated x]
    [IsFinite (pullback.snd (c ≫ x) (b ≫ x))]
    {u v : B} (huv : u ⤳ v) (hu : b u ∈ Set.range c) : b v ∈ Set.range c :=
  closure_minimal (Set.singleton_subset_iff.mpr
    (show u ∈ b ⁻¹' Set.range c from hu))
    (isClosed_preimage_range_of_finite_endpoint c x b) huv.mem_closure

end FLT.Mazur.SchemeFiniteEndpointComparison
