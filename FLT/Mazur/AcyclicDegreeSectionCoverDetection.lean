/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSectionCoverOpenLifting
public import FLT.Mazur.UnpointedAcyclicDegreeOpen

/-!
# Original fixed-degree acyclicity detected by a complete section cover

Checking the original class along covering sections constructs a lift to
its represented acyclic degree open on the whole source. This tests actual
divisor membership on every component, with the original Picard map retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  {E U T : Over (Spec (.of R))} (p : E ⟶ U) {ι : Type*} (s : ι → (U ⟶ E))
  (hc : ∀ x : E.left, ∃ i, (s i).left (p.left x) = x)
  (q : E ⟶ T) (c : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ)

include hc in
/-- Complete original sections detect the full acyclic fixed-degree divisor condition. -/
theorem acyclicDegree_mem_iff_sectionCover :
    (relativeFppfSheaf f).obj.map q.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op E) ↔
    ∀ i, (relativeFppfSheaf f).obj.map (s i ≫ q).op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op U) := by
  constructor
  · intro h i
    have hi := (acyclicDegreePicardSubfunctor f d).map (s i).op h
    change (relativeFppfSheaf f).obj.map (s i).op
      ((relativeFppfSheaf f).obj.map q.op c) ∈
        (acyclicDegreePicardSubfunctor f d).obj (op U) at hi
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hi
  · intro h
    let D := unpointedAcyclicDegreeTest f T c d
    let j : D ⟶ T := unpointedAcyclicDegreeArrow f T c d
    have ha (i : ι) := (unpointedAcyclicDegreeOpen_represents f T c d (s i ≫ q)).mp (h i)
    choose a ha _ using ha
    obtain ⟨b, hb, _⟩ := FiniteSectionCoverOpenLifting.existsUnique_lift p.left
      (fun i ↦ (s i).left) hc q.left j.left (fun i ↦ (a i).left)
      (fun i ↦ congrArg Over.Hom.left (ha i))
    have hw : b ≫ D.hom = E.hom := by
      rw [← j.w, ← Category.assoc, hb.1, q.w]
    let b' : E ⟶ D := Over.homMk b hw
    apply (unpointedAcyclicDegreeOpen_represents f T c d q).mpr
    refine ⟨b', Over.OverMorphism.ext hb.1, ?_⟩
    intro a' ha'
    exact (cancel_mono j).mp (ha'.trans (Over.OverMorphism.ext hb.1).symm)

end FLT.Mazur.CartierAbel
