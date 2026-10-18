/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraphTransport
public import FLT.Mazur.GroupActionPointTranslation
public import FLT.Mazur.PolygonActionGraph

/-!
# Every group action on an actual one-gon rotates its graph

The original pinching presentation identifies all components and all nonsmooth
points with Fin 1. Translations are automorphisms by the group-action laws,
so they preserve the unique actual component and node.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.GeneralizedCurveGraph
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {G X : Over (Spec (.of K))}
  [GrpObj G] [ModObj G X] [LocallyOfFinitePresentation X.hom]

omit [LocallyOfFinitePresentation X.hom] in
/-- The actual monoidal action specialized at any section is an automorphism. -/
theorem action_translation_isIso (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsIso (translation γ[G, X] x) := by
  rw [translation, ← GroupActionPointTranslation.translation_eq]
  exact (GroupActionPointTranslation.translationIso (X := X) x).isIso_hom

/-- A pinched one-gon has the required rotations for every genuine group action. -/
theorem rotations_of_oneGon
    (p : PolygonPinching.components K 1 ⟶ X) (q : PolygonPinching.nodes K 1 ⟶ X)
    (h : IsPushout (PolygonPinching.toComponents K 1 (by decide))
      (PolygonPinching.toNodes K 1) p q) : Rotations γ[G, X] := by
  let v := PolygonActionGraph.vertices K 1 (by decide) p q h
  let e := PolygonActionGraph.edges K 1 (by decide) p q h
  let _ : Subsingleton (irreducibleComponents X.left) := v.symm.injective.subsingleton
  let _ : Subsingleton {z : X.left // z ∉ X.hom.smoothLocus} :=
    e.symm.injective.subsingleton
  refine ⟨1, by decide, v, e, PolygonActionGraph.incidence K 1 (by decide) p q h, ?_⟩
  intro x
  let _ := action_translation_isIso (X := X) x
  let t := asIso (translation γ[G, X] x)
  refine ⟨0, ?_, ?_⟩
  · intro i
    exact congrArg Subtype.val (Subsingleton.elim (componentEquiv t (v i))
      (v (PolygonPinching.rotateIndex 0 i)))
  · intro j
    exact congrArg Subtype.val (Subsingleton.elim (nodeEquiv t (e j))
      (e (PolygonPinching.rotateIndex 0 j)))

end FLT.Mazur.GeneralizedCurveGraph
