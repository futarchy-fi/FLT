/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteExactRank
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The actual scheme of excess original frames

Pull the original (n+1)-frame scheme to an n-frame chart. Its etale projection
has exactly the incomplete chart points as its image. This retains the full
original fibers and scheme structures; it is not the moving permutation orbit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
local instance excessOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance excessOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- A larger original frame over the unchanged endpoint of a chart point. -/
def excessFrames : Scheme :=
  pullback (distinctScheme (Over.mk p) (Fin (n + 1))).hom
    (U.ι ≫ first p q (Fin n) o)

/-- Forget the larger frame but keep the original normalized chart point. -/
def excessProjection : excessFrames n o U ⟶ U.toScheme := pullback.snd _ _

instance excessProjection_etale : Etale (excessProjection n o U) := by
  unfold excessProjection excessFrames
  infer_instance

variable [QuasiCompact p]

/-- Every incomplete chart point, and only such a point, admits an excess frame. -/
theorem excessProjection_range : Set.range (excessProjection n o U) =
    (U.ι ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o)ᶜ := by
  ext x
  rw [Set.mem_compl_iff, Set.mem_preimage, not_completePoint_iff_larger_frame]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨pullback.fst (distinctScheme (Over.mk p) (Fin (n + 1))).hom
      (U.ι ≫ first p q (Fin n) o) z, ?_⟩
    exact congrArg (fun f ↦ f z) (pullback.condition
      (f := (distinctScheme (Over.mk p) (Fin (n + 1))).hom)
      (g := U.ι ≫ first p q (Fin n) o))
  · rintro ⟨y, hy⟩
    obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (distinctScheme (Over.mk p) (Fin (n + 1))).hom)
      (g := U.ι ≫ first p q (Fin n) o) y x hy
    exact ⟨z, hz⟩

/-- The excess scheme is empty exactly when the whole unchanged chart is complete. -/
theorem excessFrames_isEmpty_iff : IsEmpty (excessFrames n o U) ↔
    ∀ x : U.toScheme, U.ι x ∈ completePointLocus (p := p) (q := q) (Fin n) o := by
  constructor
  · intro h x
    by_contra hx
    have hm : x ∈ Set.range (excessProjection n o U) := by
      rw [excessProjection_range]
      exact hx
    obtain ⟨z, _⟩ := hm
    exact h.false z
  · intro h
    refine ⟨fun z ↦ ?_⟩
    have hz := Set.mem_range_self (f := excessProjection n o U) z
    rw [excessProjection_range] at hz
    exact hz (h _)

/-- A single bound eliminates actual excess schemes on every chart of every larger size. -/
theorem exists_eventually_empty_excess [TopologicalSpace.NoetherianSpace A] :
    ∃ N : ℕ, ∀ (m : ℕ) (j : Fin m) (V : (source p q (Fin m) j).Opens),
      N ≤ m → IsEmpty (excessFrames m j V) := by
  obtain ⟨N, hN⟩ := exists_eventually_complete_frames (p := p) (q := q)
  refine ⟨N, fun m j V hm ↦ (excessFrames_isEmpty_iff m j V).mpr ?_⟩
  intro x
  rw [hN m j hm]
  trivial

end FLT.Mazur.EquivalenceRelationNormalizedFrames
