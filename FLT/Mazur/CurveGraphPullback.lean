/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSums

/-!
# Graph ideals under change of parameter scheme

A point of a relative scheme gives a section of the base-changed scheme. Its
closed graph ideal commutes with every change of parameters, as an equality of
actual ideal sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.CurveGraphPullback

variable {X S T U : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- The graph of a point over the chosen base morphism. -/
def graph (x : T ⟶ X) (hx : x ≫ f = g) : T ⟶ pullback f g :=
  pullback.lift x (𝟙 _) (by simpa using hx)

@[reassoc (attr := simp)]
lemma graph_fst (x : T ⟶ X) (hx : x ≫ f = g) :
    graph f g x hx ≫ pullback.fst f g = x := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graph_snd (x : T ⟶ X) (hx : x ≫ f = g) :
    graph f g x hx ≫ pullback.snd f g = 𝟙 _ := pullback.lift_snd _ _ _

variable (h : U ⟶ S) (a : U ⟶ T) (ha : a ≫ g = h)

/-- The induced map between the actual curves over the two parameter schemes. -/
def curveMap : pullback f h ⟶ pullback f g :=
  pullback.lift (pullback.fst f h) (pullback.snd f h ≫ a) (by
    rw [Category.assoc, ha, pullback.condition])

@[reassoc (attr := simp)]
lemma curveMap_fst : curveMap f g h a ha ≫ pullback.fst f g = pullback.fst f h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma curveMap_snd : curveMap f g h a ha ≫ pullback.snd f g = pullback.snd f h ≫ a :=
  pullback.lift_snd _ _ _

/-- The induced map is an actual base-change square. -/
theorem curveMap_isPullback :
    IsPullback (curveMap f g h a ha) (pullback.snd f h) (pullback.snd f g) a := by
  apply IsPullback.of_right (h₁₂ := pullback.fst f g) (h₂₂ := g)
    (v₁₃ := f) ?_ (by simp) (IsPullback.of_hasPullback f g)
  simpa only [curveMap_fst, ha] using IsPullback.of_hasPullback f h

variable (x : T ⟶ X) (hx : x ≫ f = g)

include ha hx in
/-- The point over the new parameters satisfies the required base equation. -/
lemma point_over : (a ≫ x) ≫ f = h := by rw [Category.assoc, hx, ha]

/-- The graph square commutes as morphisms of schemes. -/
@[reassoc]
lemma graph_curveMap :
    graph f h (a ≫ x) (point_over f g h a ha x hx) ≫ curveMap f g h a ha =
      a ≫ graph f g x hx := by
  apply pullback.hom_ext <;> simp

/-- Base change of a graph is the graph of the pulled-back point. -/
theorem graph_isPullback :
    IsPullback (graph f h (a ≫ x) (point_over f g h a ha x hx)) a
      (curveMap f g h a ha) (graph f g x hx) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd f h) (h₂₂ := pullback.snd f g)
    (v₁₃ := a) ?_ (graph_curveMap f g h a ha x hx)
    (curveMap_isPullback f g h a ha).flip
  simp only [graph_snd]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The equality is of actual graph ideals; no chosen divisor comparison is input. -/
theorem graph_ker_comap [IsSeparated f] :
    (graph f g x hx).ker.comap (curveMap f g h a ha) =
      (graph f h (a ≫ x) (point_over f g h a ha x hx)).ker := by
  let _ := FCurve.isClosedImmersion_section (pullback.snd f g) (graph f g x hx)
    (graph_snd f g x hx)
  let H := graph_isPullback f g h a ha x hx
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

end FLT.Mazur.CurveGraphPullback
