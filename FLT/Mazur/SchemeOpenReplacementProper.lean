/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenReplacementPreimage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness of a replacement inside an arbitrary exterior

Properness is local on the target. The full pullback over the exterior is
its identity, while the full pullback over the old chart is the given
proper local modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeOpenReplacement
universe u
variable {O E B M : Scheme.{u}} (e : O ⟶ E) (b : O ⟶ B) (j : O ⟶ M)
  [IsOpenImmersion e] [IsOpenImmersion b] [IsOpenImmersion j]
  (f : M ⟶ B) (h : j ≫ f = b)

/-- The original exterior and replaced chart cover the target. -/
def targetCover : (pushout e b).OpenCover where
  I₀ := Bool
  X i := if i then B else E
  f i := by
    cases i
    · exact pushout.inl e b
    · exact pushout.inr e b
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    constructor
    · intro z
      rcases SchemeOpenPushout.charts_cover e b z with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact ⟨false, a, ha⟩
      · exact ⟨true, a, ha⟩
    · intro i
      cases i <;> dsimp <;> infer_instance

/-- Proper local replacement remains proper after gluing to any retained exterior. -/
theorem contraction_isProper (hf : f ⁻¹' Set.range b = Set.range j) [IsProper f] :
    IsProper (contraction e b j f h) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (targetCover e b)
  intro i
  cases i with
  | false =>
    change IsProper (pullback.snd (contraction e b j f h) (pushout.inl e b))
    rw [← (isPullback_inl e b j f h hf).flip.isoPullback_inv_snd]
    infer_instance
  | true =>
    change IsProper (pullback.snd (contraction e b j f h) (pushout.inr e b))
    rw [← (isPullback_inr e b j f h).flip.isoPullback_inv_snd]
    infer_instance

end FLT.Mazur.SchemeOpenReplacement
