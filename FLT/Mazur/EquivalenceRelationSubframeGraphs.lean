/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedFrameRelation
public import FLT.Mazur.EquivalenceRelationNormalizedSubframe

/-!
# Open subframe graphs in the full mixed relation

Each label embedding defines an open graph with both independently sized frames
and the unchanged original arrow. These graphs are pairwise disjoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

/-- The graph of a moving subframe, using its actual original distinguished arrow. -/
def subframeGraph (ι : J ↪ I) : source p q I o ⟶ relation p q I J o o' :=
  lift p q I J o o' (𝟙 _) (subframeMap e o o' ι) (coordinate p q I o (ι o'))
    (by rw [Category.id_comp]; exact coordinate_first p q I o (ι o'))
    (subframeMap_first e o o' ι).symm

/-- The first frame is kept on each graph. -/
@[reassoc] theorem subframeGraph_fst (ι : J ↪ I) :
    subframeGraph e o o' ι ≫ fst p q I J o o' = 𝟙 _ :=
  lift_fst p q I J o o' _ _ _ _ _

/-- The independently sized second frame is exactly the moving subframe. -/
@[reassoc] theorem subframeGraph_snd (ι : J ↪ I) :
    subframeGraph e o o' ι ≫ snd p q I J o o' = subframeMap e o o' ι :=
  lift_snd p q I J o o' _ _ _ _ _

/-- Each graph retains its original arrow as a scheme morphism. -/
@[reassoc] theorem subframeGraph_arrow (ι : J ↪ I) :
    subframeGraph e o o' ι ≫ arrow p q I J o o' = coordinate p q I o (ι o') :=
  lift_arrow p q I J o o' _ _ _ _ _

include e in
/-- The first projection of the full mixed relation is etale. -/
theorem fst_etale [Etale p] : Etale (fst p q I J o o') := by
  let _ := first_etale e J o'
  change Etale (pullback.fst (leftRelationTarget p q I o) (first p q J o') ≫
    pullback.fst (first p q I o) p)
  infer_instance

/-- Each embedding graph is an open subscheme of the entire original mixed relation. -/
theorem subframeGraph_isOpenImmersion [Etale p] (ι : J ↪ I) :
    IsOpenImmersion (subframeGraph e o o' ι) := by
  let _ := fst_etale e o o'
  exact UnramifiedSectionImmersion.isOpenImmersion (fst p q I J o o') _
    (subframeGraph_fst e o o' ι)

variable {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')

/-- The exact subframe equation factors the entire original arrow through its graph. -/
theorem subframeGraph_factor (ι : J ↪ I)
    (h : (z ≫ fst p q I J o o') ≫ subframeMap e o o' ι = z ≫ snd p q I J o o') :
    (z ≫ fst p q I J o o') ≫ subframeGraph e o o' ι = z := by
  apply hom_ext p q I J o o' e
  · rw [Category.assoc, subframeGraph_fst, Category.comp_id]
  · rw [Category.assoc, subframeGraph_snd]
    exact h

/-- A nonempty mixed test belongs to at most one embedding graph. -/
theorem subframeGraph_unique [Nonempty T] (ι κ : J ↪ I)
    (hι : ∃ u, u ≫ subframeGraph e o o' ι = z)
    (hκ : ∃ v, v ≫ subframeGraph e o o' κ = z) : ι = κ := by
  obtain ⟨u, rfl⟩ := hι
  obtain ⟨v, hv⟩ := hκ
  have h : v = u := by
    simpa only [Category.assoc, subframeGraph_fst, Category.comp_id] using
      congrArg (fun f ↦ f ≫ fst p q I J o o') hv
  subst v
  apply subframeMap_unique e o o' u
  exact (by simpa only [Category.assoc, subframeGraph_snd] using
    congrArg (fun f ↦ f ≫ snd p q I J o o') hv.symm)

/-- Distinct label selections give disjoint open graphs, even for unequal frame sizes. -/
theorem subframeGraph_disjoint [Etale p] (ι κ : J ↪ I) (h : ι ≠ κ) :
    Disjoint (Set.range (subframeGraph e o o' ι)) (Set.range (subframeGraph e o o' κ)) := by
  let _ := subframeGraph_isOpenImmersion e o o' ι
  let _ := subframeGraph_isOpenImmersion e o o' κ
  apply Set.disjoint_left.mpr
  intro x hx hy
  let z := (relation p q I J o o').fromSpecResidueField x
  have hι : Set.range z ⊆ Set.range (subframeGraph e o o' ι) := by
    rintro _ ⟨t, rfl⟩
    simpa only [z, Scheme.fromSpecResidueField_apply] using hx
  have hκ : Set.range z ⊆ Set.range (subframeGraph e o o' κ) := by
    rintro _ ⟨t, rfl⟩
    simpa only [z, Scheme.fromSpecResidueField_apply] using hy
  exact h (subframeGraph_unique e o o' z ι κ
    ⟨IsOpenImmersion.lift _ z hι, IsOpenImmersion.lift_fac _ z hι⟩
    ⟨IsOpenImmersion.lift _ z hκ, IsOpenImmersion.lift_fac _ z hκ⟩)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
