/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeGraphs

/-!
# Common-frame graphs in the entire mixed relation

Two embeddings select independently sized subframes from one normalized source.
The resulting graph retains the actual original arrow. Jointly exhaustive label
embeddings make it a monomorphism; every such graph is etale.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)
  (α : I ↪ H) (β : J ↪ H)

/-- Both selected frames, together with the unchanged arrow between their first endpoints. -/
def jointGraph : source p q H (α o) ⟶ relation p q I J o o' :=
  lift p q I J o o' (subframeMap e (α o) o α) (subframeMap e (α o) o' β)
    (coordinate p q H (α o) (β o'))
    (by rw [coordinate_first, subframeMap_first, ← first_eq_distinguished])
    (subframeMap_first e (α o) o' β).symm

/-- The first independent frame is the first selected subframe. -/
@[reassoc] theorem jointGraph_fst :
    jointGraph e o o' α β ≫ fst p q I J o o' = subframeMap e (α o) o α :=
  lift_fst p q I J o o' _ _ _ _ _

/-- The second independent frame is the second selected subframe. -/
@[reassoc] theorem jointGraph_snd :
    jointGraph e o o' α β ≫ snd p q I J o o' = subframeMap e (α o) o' β :=
  lift_snd p q I J o o' _ _ _ _ _

/-- The graph retains its actual original arrow, including all coefficient maps. -/
@[reassoc] theorem jointGraph_arrow :
    jointGraph e o o' α β ≫ arrow p q I J o o' = coordinate p q H (α o) (β o') :=
  lift_arrow p q I J o o' _ _ _ _ _

/-- The common frame is normalized at precisely the first original endpoint. -/
@[reassoc] theorem jointGraph_first :
    jointGraph e o o' α β ≫ fst p q I J o o' ≫ first p q I o = first p q H (α o) := by
  rw [← Category.assoc, jointGraph_fst, subframeMap_first, ← first_eq_distinguished]

/-- Joint exhaustion makes the common-frame graph a monomorphism on all scheme tests. -/
theorem jointGraph_mono (h : ∀ k, (∃ i, α i = k) ∨ ∃ j, β j = k) :
    Mono (jointGraph e o o' α β) where
  right_cancellation u v huv := by
    apply hom_ext_second p q H (α o) e
    intro k
    rcases h k with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have hi := congrArg (fun z ↦ z ≫ fst p q I J o o' ≫ coordinate p q I o i ≫ q) huv
      simpa only [jointGraph_fst_assoc, Category.assoc, subframeMap_second] using hi
    · have hj := congrArg (fun z ↦ z ≫ snd p q I J o o' ≫ coordinate p q J o' j ≫ q) huv
      simpa only [jointGraph_snd_assoc, Category.assoc, subframeMap_second] using hj

/-- The comparison is etale over the full mixed relation, with no complete-support assumption. -/
theorem jointGraph_etale [Etale p] : Etale (jointGraph e o o' α β) := by
  let _ := fst_etale e o o'
  let _ := first_etale e I o
  let _ := first_etale e H (α o)
  have : Etale (jointGraph e o o' α β ≫ fst p q I J o o' ≫ first p q I o) := by
    rw [jointGraph_first]
    infer_instance
  exact Etale.of_comp _ (fst p q I J o o' ≫ first p q I o)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
