/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFrameNormalization
public import FLT.Mazur.EquivalenceRelationJointFrameGraph
public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison
public import FLT.Mazur.RelativeJointGeometricFrame

/-!
# Every original geometric arrow has a bounded common-frame lift

Transport the first frame along the whole original arrow, take its union with
the independent second frame, and normalize the union at the first frame's
original distinguished endpoint. This covers incomplete frames of arbitrary sizes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

local instance jointOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance jointOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- Every full geometric mixed arrow is a graph of two subframes of a bounded common frame. -/
theorem exists_joint_original_frame {K : Type} [Field K]
    (z : Spec (.of K) ⟶ relation p q I J o o') :
    ∃ (n : ℕ) (_ : n ≤ Fintype.card I + Fintype.card J)
      (α : I ↪ Fin n) (β : J ↪ Fin n),
      (∀ k, (∃ i, α i = k) ∨ ∃ j, β j = k) ∧
      ∃ w : Spec (.of K) ⟶ source p q (Fin n) (α o),
        w ≫ jointGraph e o o' α β = z := by
  let u := z ≫ fst p q I J o o'
  let v := z ≫ snd p q I J o o'
  let a := z ≫ arrow p q I J o o'
  have ha : a ≫ p = u ≫ first p q I o := by
    simp only [a, u, Category.assoc, arrow_first]
  have hb : a ≫ q = v ≫ first p q J o' := by
    simp only [a, v, Category.assoc, arrow_second]
  let _ : Subsingleton (Over.mk (a ≫ q)).left :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  let _ : Nonempty (Over.mk (a ≫ q)).left := inferInstanceAs (Nonempty (Spec (.of K)))
  obtain ⟨n, hn, α, β, w, hw₁, hw₂, hw⟩ := exists_joint_geometric_frame (Over.mk p)
    (comparisonFrame e I o u a ha) (targetFrame J o' v a hb)
  refine ⟨n, hn, α, β, hw, normalizeFrame e (Fin n) (α o) w, ?_⟩
  apply hom_ext p q I J o o' e
  · rw [Category.assoc, jointGraph_fst]
    apply hom_ext_second p q I o e
    intro i
    rw [Category.assoc, normalizeFrame_subframe_second]
    have hi := congrArg (fun t ↦ (t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q) hw₁
    simp only [Category.assoc, subframe_coordinate] at hi
    rw [hi]
    change (rebaseFrame e I a (frameCast I ha.symm (testFrame I o u)) ≫
      distinctCoordinate (Over.mk p) I i).left ≫ q = _
    rw [rebaseFrame_second]
    simp only [testFrame, frameCast, framePull, frame,
      Over.homMk_left, Over.comp_left, coordinate, Category.assoc, u]
  · rw [Category.assoc, jointGraph_snd]
    apply hom_ext_second p q J o' e
    intro j
    rw [Category.assoc, normalizeFrame_subframe_second]
    have hj := congrArg (fun t ↦ (t ≫ distinctCoordinate (Over.mk p) J j).left ≫ q) hw₂
    simp only [Category.assoc, subframe_coordinate] at hj
    rw [hj]
    simp only [targetFrame, testFrame, frameCast, framePull, frame,
      Over.homMk_left, Over.comp_left, coordinate, Category.assoc, v]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
