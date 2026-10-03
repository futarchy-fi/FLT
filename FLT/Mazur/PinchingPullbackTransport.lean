/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonAtlas
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Transport for the base-changed pinching span

Parameter-first pullbacks are compared with the specified over-category
pullbacks. Cocone compatibility identifies the two actual endpoint sections.
The split node leg reduces the pushout property to normalization descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
namespace FLT.Mazur.PinchingPullbackTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {B T : Scheme.{u}} (g : T ⟶ B)
/-- Reverse the factors to match the over-category pullback convention. -/
def swap (X : Over B) : Over.mk (pullback.fst g X.hom) ≅ (Over.pullback g).obj X :=
  Over.isoMk (pullbackSymmetry g X.hom) (by simp)
@[reassoc (attr := simp)] theorem swap_fst (X : Over B) :
    (swap g X).hom.left ≫ pullback.fst _ _ = pullback.snd _ _ := by simp [swap]
@[reassoc (attr := simp)] theorem swap_snd (X : Over B) :
    (swap g X).hom.left ≫ pullback.snd _ _ = pullback.fst _ _ := by simp [swap]
/-- Compare a parameter-first product with base change of an isomorphic object. -/
def comparison {X Y : Over B} (e : X ≅ Y) :
    Over.mk (pullback.fst g X.hom) ≅ (Over.pullback g).obj Y :=
  swap g X ≪≫ (Over.pullback g).mapIso e
@[reassoc (attr := simp)] theorem comparison_fst {X Y : Over B} (e : X ≅ Y) :
    (comparison g e).hom.left ≫ pullback.fst _ _ = pullback.snd _ _ ≫ e.hom.left := by
  simp [comparison, Over.pullback]
@[reassoc (attr := simp)] theorem comparison_snd {X Y : Over B} (e : X ≅ Y) :
    (comparison g e).hom.left ≫ pullback.snd _ _ = pullback.fst _ _ := by
  simp [comparison, Over.pullback]
/-- The constant section induced by a section over the original base. -/
def sectionMap {X : Over B} (s : Over.mk (𝟙 B) ⟶ X) : T ⟶ ((Over.pullback g).obj X).left :=
  pullback.lift (g ≫ s.left) (𝟙 _) (by simp)
@[reassoc] theorem sectionMap_map {X Y : Over B}
    (s : Over.mk (𝟙 B) ⟶ X) (f : X ⟶ Y) :
    sectionMap g s ≫ ((Over.pullback g).map f).left = sectionMap g (s ≫ f) := by
  apply pullback.hom_ext <;> simp [sectionMap, Over.pullback]
variable (K : Type u) [Field K] (n : ℕ)
/-- Choose the zero branch over every node. -/
def nodeRetraction : PolygonPinching.nodes K n ⟶ PolygonPinching.branches K n :=
  Sigma.desc fun i ↦ PolygonPinching.branchι K n i false
theorem nodeRetraction_toNodes :
    nodeRetraction K n ≫ PolygonPinching.toNodes K n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  simp [nodeRetraction, PolygonPinching.nodeι]
instance toNodes_epi {T : Scheme.{u}} (g : T ⟶ Spec (.of K)) :
    Epi ((Over.pullback g).map (PolygonPinching.toNodes K n)) := by
  apply epi_of_epi_fac (f := (Over.pullback g).map (nodeRetraction K n)) (h := 𝟙 _)
  rw [← Functor.map_comp, nodeRetraction_toNodes, CategoryTheory.Functor.map_id]
variable {T : Scheme.{u}} (g : T ⟶ Spec (.of K)) (hn : 0 < n)
include hn in
theorem input_condition {Y : Over T}
    (f : (Over.pullback g).obj (PolygonPinching.components K n) ⟶ Y)
    (q : (Over.pullback g).obj (PolygonPinching.nodes K n) ⟶ Y)
    (w : (Over.pullback g).map (PolygonPinching.toComponents K n hn) ≫ f =
      (Over.pullback g).map (PolygonPinching.toNodes K n) ≫ q) (j : Fin n) :
    sectionMap g (PolygonPinching.endpoint K n hn j false) ≫ f.left =
      sectionMap g (PolygonPinching.endpoint K n hn j true) ≫ f.left := by
  have hw (b : Bool) := congrArg (fun t ↦ sectionMap g (PolygonPinching.branchι K n j b) ≫ t.left) w
  simp only [Over.comp_left, ← Category.assoc, sectionMap_map] at hw
  simp only [PolygonPinching.branchι_toNodes] at hw
  simpa [PolygonPinching.branchι, PolygonPinching.toComponents] using
    (hw false).trans (hw true).symm
end FLT.Mazur.PinchingPullbackTransport

namespace FLT.Mazur.PinchingPushoutCriterion
variable {C : Type u} [Category.{v} C] {A B D P : C}
  (a : A ⟶ B) (b : A ⟶ D) (p : B ⟶ P) (q : D ⟶ P) [Epi b]
theorem isPushout_of_existsUnique (w : a ≫ p = b ≫ q)
    (h : ∀ (Y : C) (f : B ⟶ Y) (g : D ⟶ Y), a ≫ f = b ≫ g →
      ∃! d : P ⟶ Y, p ≫ d = f) : IsPushout a b p q := by
  classical
  let d (s : PushoutCocone a b) := (h s.pt s.inl s.inr s.condition).choose
  have hd (s : PushoutCocone a b) : p ≫ d s = s.inl :=
    (h s.pt s.inl s.inr s.condition).choose_spec.1
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ d hd ?_ ?_⟩⟩
  · intro s
    apply (cancel_epi b).mp
    rw [← Category.assoc, ← w, Category.assoc, hd, s.condition]
  · intro s m hm _
    exact (h s.pt s.inl s.inr s.condition).choose_spec.2 m hm
end FLT.Mazur.PinchingPushoutCriterion
