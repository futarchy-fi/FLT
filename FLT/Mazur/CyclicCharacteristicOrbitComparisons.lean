/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbit
public import FLT.Mazur.CyclicCharacteristicUnmarkedRelation

/-!
# Full comparison orbits contain every actual unmarked comparison

Evaluating the original classifying parameter at a point gives an actual
comparison point. In particular the finite relabeling fibers lie in full orbits.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- A compatible comparison on a scheme test relates the images of each test point. -/
theorem related_of_unmarked {T : Scheme} {b c : Bool}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    (h : UnmarkedRelated n b c q r) (x : T) :
    Related n (normalizedDisjointInclusion n b (q x))
      (normalizedDisjointInclusion n c (r x)) := by
  obtain ⟨i⟩ := h
  let a : ProductArrow n q r := productCompatibleParameter n b c q r i
  refine ⟨(a.val ≫ disjointComparisonInclusion n b c) x, ?_, ?_⟩
  · have he : a.val ≫ disjointComparisonInclusion n b c ≫ disjointComparisonSource n =
        q ≫ normalizedDisjointInclusion n b := by
      rw [disjointComparisonInclusion_source, ← Category.assoc, productArrow_source]
    exact congrArg (fun k ↦ k x) he
  · have he : a.val ≫ disjointComparisonInclusion n b c ≫ disjointComparisonTarget n =
        r ≫ normalizedDisjointInclusion n c := by
      rw [disjointComparisonInclusion_target, ← Category.assoc, productArrow_target]
    exact congrArg (fun k ↦ k x) he

/-- Finite relabeling identifies points already joined by the actual full comparison scheme. -/
theorem related_relabel (b : Bool) (g : RelabelGroup n) (x : normalizedLocus n b) :
    Related n (normalizedDisjointInclusion n b ((normalizedRelabelAction n b g).hom x))
      (normalizedDisjointInclusion n b x) :=
  related_of_unmarked n (unmarkedRelated_relabel n b (𝟙 _) g) x

/-- Every original finite quotient fiber lies in one full comparison orbit. -/
theorem projection_eq_of_finite_quotient_eq (b : Bool) (x y : normalizedLocus n b)
    (h : normalizedQuotientMap n b x = normalizedQuotientMap n b y) :
    projection n (normalizedDisjointInclusion n b x) =
      projection n (normalizedDisjointInclusion n b y) := by
  obtain ⟨g, rfl⟩ := (normalizedQuotientMap_eq_iff_orbit n b x y).mp h
  exact ((projection_eq_iff n _ _).mpr (related_relabel n b g x)).symm

end FLT.Mazur.CyclicCharacteristicOrbit
