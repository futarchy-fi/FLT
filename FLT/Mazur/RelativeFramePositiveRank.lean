/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameExactRank
public import FLT.Mazur.RelativeSingletonFrame

/-!
# Positive exact ranks of surjective relative schemes

The one-frame image is the actual image of the original morphism. A
surjective morphism therefore has no rank-zero points, without any
Noetherian or reducedness assumption on its base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]

/-- A single distinct coordinate has exactly the original morphism's image. -/
theorem rankImageOpen_one_range :
    (rankImageOpen E 1 : Set S) = Set.range E.hom := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨(distinctCoordinate E (Fin 1) 0).left z,
      congrArg (fun f ↦ f z) (distinctCoordinate E (Fin 1) 0).w⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨(singletonFrame E (𝟙 E)).left z,
      congrArg (fun f ↦ f z) (singletonFrame E (𝟙 E)).w⟩

/-- Surjectivity supplies a one-frame at every original point. -/
theorem rankImageOpen_one_eq_top (h : Function.Surjective E.hom) :
    rankImageOpen E 1 = ⊤ := by
  apply TopologicalSpace.Opens.ext
  rw [rankImageOpen_one_range, Set.range_eq_univ.mpr h]
  rfl

/-- The full rank-zero locus of a surjective morphism is empty. -/
theorem exactRank_zero_eq_empty (h : Function.Surjective E.hom) :
    exactRank E 0 = ∅ := by
  ext z
  simp only [exactRank, rankAtMost, zero_add, rankImageOpen_one_eq_top E h,
    TopologicalSpace.Opens.coe_top, Set.compl_univ, Set.inter_empty, Set.mem_empty_iff_false]

/-- Every actual exact rank of a surjective morphism is strictly positive. -/
theorem exactRank_pos (h : Function.Surjective E.hom) {z : S} {n : ℕ}
    (hz : z ∈ exactRank E n) : 0 < n := by
  apply Nat.pos_of_ne_zero
  intro hn
  rw [hn, exactRank_zero_eq_empty E h] at hz
  exact hz

end FLT.Mazur.RelativeOrderedTuples
