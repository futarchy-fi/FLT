/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Empty intersections survive arbitrary change of the ambient scheme

Disjoint ranges give an empty scheme intersection after any base change.
No flatness or reducedness hypothesis is required.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SchemeDisjointBaseChange
universe u
variable {X Y Z Z' : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
  (h : Disjoint (Set.range f) (Set.range g)) (q : Z' ⟶ Z)

include h in
/-- Points in the two extended images would give a point in both original images. -/
theorem disjoint :
    Disjoint (Set.range (pullback.fst q f)) (Set.range (pullback.fst q g)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  apply Set.disjoint_left.mp h
  · exact ⟨pullback.snd q f a, rfl⟩
  · refine ⟨pullback.snd q g b, ?_⟩
    have hf := congrArg (fun k : pullback q f ⟶ Z => k a) pullback.condition
    have hg := congrArg (fun k : pullback q g ⟶ Z => k b) pullback.condition
    exact hg.symm.trans ((congrArg q hb).trans hf)

include h in
/-- The entire intersection after base change is the empty scheme. -/
theorem isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _)
      (pullback.fst q f) (pullback.fst q g) := by
  let _ := Scheme.isEmpty_pullback _ _ (disjoint h q)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (pullback.fst q f) (pullback.fst q g))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

/-- The empty-intersection comparison retains the actual extended fiber product. -/
def pullbackIso : (∅ : Scheme) ≅ pullback (pullback.fst q f) (pullback.fst q g) :=
  (isPullback h q).isoPullback

end FLT.Mazur.SchemeDisjointBaseChange
