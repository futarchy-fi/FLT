/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseGrading

/-!
# The original algebra inclusion for a multiple Veronese step

The inclusion sends retained degree d to degree r*d and keeps the actual
compatible section. Recomposition detects its ring laws and injectivity.
-/

@[expose] public noncomputable section
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval
variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q r : ℕ)

/-- The common retained piece is the same original section with a reindexed degree. -/
def multipleVeroneseDegreeInclusion (d : ℕ) :
    compatibleVeroneseDegree R n h (q * r) d →+
      compatibleVeroneseDegree R n h q (r * d) where
  toFun s := ⟨s.val, by
    change s.val ∈ compatibleSectionDegree R n h (q * (r * d))
    rw [← Nat.mul_assoc]
    exact s.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Insert common degrees into their actual places in the original direct sum. -/
def multipleVeroneseAddInclusion :
    CompatibleVeroneseSections R n h (q * r) →+ CompatibleVeroneseSections R n h q :=
  DirectSum.toAddMonoid fun d ↦
    (DirectSum.of (compatibleVeroneseDegree R n h q ·) (r * d)).comp
      (multipleVeroneseDegreeInclusion R n h q r d)

/-- Additive reindexing sends a summand to its actual multiplied degree. -/
theorem multipleVeroneseAddInclusion_of (d : ℕ)
    (s : compatibleVeroneseDegree R n h (q * r) d) :
    multipleVeroneseAddInclusion R n h q r (DirectSum.of _ d s) =
      DirectSum.of (compatibleVeroneseDegree R n h q ·) (r * d)
        (multipleVeroneseDegreeInclusion R n h q r d s) :=
  DirectSum.toAddMonoid_of _ _ _

/-- Reindexing retains the actual compatible section before any stage evaluation. -/
theorem multipleVeroneseAddInclusion_recompose
    (s : CompatibleVeroneseSections R n h (q * r)) :
    compatibleVeroneseToSections R n h q (multipleVeroneseAddInclusion R n h q r s) =
      compatibleVeroneseToSections R n h (q * r) s := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d s =>
    rw [multipleVeroneseAddInclusion_of]
    change DirectSum.coeRingHom (compatibleVeroneseDegree R n h q)
      (DirectSum.of _ (r * d) (multipleVeroneseDegreeInclusion R n h q r d s)) =
        DirectSum.coeRingHom (compatibleVeroneseDegree R n h (q * r)) (DirectSum.of _ d s)
    rw [DirectSum.coeRingHom_of, DirectSum.coeRingHom_of]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

variable [NeZero q]

/-- The original common-degree inclusion preserves the unit and multiplication. -/
def multipleVeroneseInclusion :
    CompatibleVeroneseSections R n h (q * r) →+* CompatibleVeroneseSections R n h q where
  toFun := multipleVeroneseAddInclusion R n h q r
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    apply compatibleVeroneseToSections_injective R n h q (NeZero.pos q)
    rw [multipleVeroneseAddInclusion_recompose, map_one, map_one]
  map_mul' s t := by
    apply compatibleVeroneseToSections_injective R n h q (NeZero.pos q)
    rw [multipleVeroneseAddInclusion_recompose, map_mul, map_mul,
      multipleVeroneseAddInclusion_recompose, multipleVeroneseAddInclusion_recompose]

/-- A homogeneous insertion stays the same section at its multiplied degree. -/
theorem multipleVeroneseInclusion_of (d : ℕ) (s : compatibleVeroneseDegree R n h (q * r) d) :
    multipleVeroneseInclusion R n h q r (DirectSum.of _ d s) =
      DirectSum.of (compatibleVeroneseDegree R n h q ·) (r * d)
        (multipleVeroneseDegreeInclusion R n h q r d s) :=
  multipleVeroneseAddInclusion_of R n h q r d s

/-- The inclusion multiplies the internal homogeneous degree by the actual step ratio. -/
theorem multipleVeroneseInclusion_mem (d : ℕ)
    (s : CompatibleVeroneseSections R n h (q * r))
    (hs : s ∈ compatibleVeroneseGrade R n h (q * r) d) :
    multipleVeroneseInclusion R n h q r s ∈ compatibleVeroneseGrade R n h q (r * d) := by
  obtain ⟨t, rfl⟩ := hs
  exact ⟨_, (multipleVeroneseInclusion_of R n h q r d t).symm⟩

/-- Every section of a common homogeneous degree comes from its original retained summand. -/
theorem multipleVeroneseInclusion_homogeneous_surjective (d : ℕ)
    (s : CompatibleVeroneseSections R n h q)
    (hs : s ∈ compatibleVeroneseGrade R n h q (r * d)) :
    ∃ t ∈ compatibleVeroneseGrade R n h (q * r) d,
      multipleVeroneseInclusion R n h q r t = s := by
  obtain ⟨t, rfl⟩ := hs
  let u : compatibleVeroneseDegree R n h (q * r) d := ⟨t.val, by
    change t.val ∈ compatibleSectionDegree R n h (q * r * d)
    rw [Nat.mul_assoc]
    exact t.property⟩
  refine ⟨DirectSum.of _ d u, ⟨u, rfl⟩, ?_⟩
  rw [multipleVeroneseInclusion_of]
  rfl

/-- Every original finite-stage evaluation is unchanged by the inclusion. -/
theorem multipleVeroneseInclusion_eval (m : ℕ) (s : CompatibleVeroneseSections R n h (q * r)) :
    compatibleVeroneseEval R n h q m (multipleVeroneseInclusion R n h q r s) =
      compatibleVeroneseEval R n h (q * r) m s :=
  congrArg (compatibleEval R n h m) (multipleVeroneseAddInclusion_recompose R n h q r s)

/-- Positive common-step algebras embed into the original retained algebra. -/
theorem multipleVeroneseInclusion_injective (hr : 0 < r) :
    Function.Injective (multipleVeroneseInclusion R n h q r) := by
  intro s t he
  apply compatibleVeroneseToSections_injective R n h (q * r) (Nat.mul_pos (NeZero.pos q) hr)
  exact (multipleVeroneseAddInclusion_recompose R n h q r s).symm.trans
    ((congrArg (compatibleVeroneseToSections R n h q) he).trans
      (multipleVeroneseAddInclusion_recompose R n h q r t))

end FLT.Mazur.PolygonInfinitesimalStages
