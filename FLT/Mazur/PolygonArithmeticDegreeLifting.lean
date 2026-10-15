/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticUniformLifting
public import FLT.Mazur.PolygonArithmeticCompatibleReduction
public import FLT.Mazur.SurjectiveTowerLifting

/-!
# Lifting actual homogeneous sections to compatible formal sections

The uniform adjacent lifting theorem extends every sufficiently positive
homogeneous section to a compatible homogeneous section across all stages.
The resulting element belongs to the already constructed graded algebra.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family stageRestriction
  boundaryLineSystemIso

/-- Transport of the actual section map along equal scheme morphisms. -/
theorem boundarySectionMap_transport {X Y : Scheme} {f g : X ⟶ Y} (hf : f = g)
    {L : Y.Modules} {M : X.Modules}
    (he : ((Scheme.Modules.pullback f).obj L ≅ M) =
      ((Scheme.Modules.pullback g).obj L ≅ M))
    (e : (Scheme.Modules.pullback f).obj L ≅ M) (d : ℕ) (s : Piece L ⊤ d) :
    SectionGradedLinePullback.sectionMap f e d ⊤ s =
      SectionGradedLinePullback.sectionMap g (he.mp e) d ⊤ s := by
  subst g
  rfl

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Restriction on the actual homogeneous submodule of a fixed degree. -/
def boundaryDegreeTransition (d : ℕ) {a b : ℕ} (hab : a ≤ b) :
    grade (boundaryLine A π b n h) ⊤ d → grade (boundaryLine A π a n h) ⊤ d :=
  fun s ↦ ⟨boundarySectionsMap A π n h (homOfLE hab) s,
    boundarySectionsMap_mem_grade A π n h (homOfLE hab) s.property⟩

/-- The adjacent ring map is the specified tensor-degree section map. -/
theorem boundarySectionsMap_adjacent_of (m d : ℕ)
    (s : Piece (boundaryLine A π (m + 1) n h) ⊤ d) :
    boundarySectionsMap A π n h (homOfLE (Nat.le_succ m))
      (of (boundaryLine A π (m + 1) n h) ⊤ d s) =
    of (boundaryLine A π m n h) ⊤ d
      (SectionGradedLinePullback.sectionMap (stageRestriction A π m n h)
        (adjacentBoundaryLineIso A π m n h) d ⊤ s) := by
  have hf : (stageSystem A π n h).map (homOfLE (Nat.le_succ m)) =
      stageRestriction A π m n h := Functor.ofSequence_map_homOfLE_succ _ m
  have he : ((Scheme.Modules.pullback
      ((stageSystem A π n h).map (homOfLE (Nat.le_succ m)))).obj
        (boundaryLine A π (m + 1) n h) ≅ boundaryLine A π m n h) =
      ((Scheme.Modules.pullback (stageRestriction A π m n h)).obj
        (boundaryLine A π (m + 1) n h) ≅ boundaryLine A π m n h) := by rw [hf]
  exact (SectionGradedLinePullback.ringHom_of _
    (boundaryLineSystemIso A π n h (homOfLE (Nat.le_succ m))) d s).trans
      (congrArg (of (boundaryLine A π m n h) ⊤ d)
        (boundarySectionMap_transport hf he _ d s))

/-- Adjacent section lifting is surjectivity on the original homogeneous submodule. -/
theorem boundaryDegreeTransition_surjective (m d : ℕ)
    (hs : Function.Surjective
      (SectionGradedLinePullback.sectionMap (stageRestriction A π m n h)
        (adjacentBoundaryLineIso A π m n h) d ⊤)) :
    Function.Surjective (boundaryDegreeTransition A π n h d (Nat.le_succ m)) := by
  intro s
  obtain ⟨t, ht⟩ := s.property
  obtain ⟨u, hu⟩ := hs t
  refine ⟨⟨of (boundaryLine A π (m + 1) n h) ⊤ d u, ⟨u, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact (boundarySectionsMap_adjacent_of A π n h m d u).trans
    ((congrArg (of (boundaryLine A π m n h) ⊤ d) hu).trans ht)

variable [NeZero n] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)

include hne hgen in
/-- Every sufficiently positive stage section lifts to the constructed compatible degree. -/
theorem compatibleDegree_uniformLifting : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : grade (boundaryLine A π m n h) ⊤ d,
      ∃ t : compatibleSectionDegree A π n h d, compatibleEval A π n h m t = s := by
  obtain ⟨N, hN⟩ := boundarySections_uniformSurjective A π hne hgen n h
  refine ⟨N, fun d hd m s ↦ ?_⟩
  obtain ⟨t, ht, htm⟩ := SurjectiveTowerLifting.exists_compatible
    (boundaryDegreeTransition A π n h d)
    (fun a ↦ boundaryDegreeTransition_surjective A π n h a d (hN d hd a))
    (fun a x ↦ Subtype.ext (by
      change boundarySectionsMap A π n h (𝟙 a) x = x
      rw [boundarySectionsMap_id]; rfl))
    (fun hab hbc x ↦ Subtype.ext (by
      change boundarySectionsMap A π n h (homOfLE hab)
        (boundarySectionsMap A π n h (homOfLE hbc) x) = _
      exact (DFunLike.congr_fun (boundarySectionsMap_comp A π n h
        (homOfLE hab) (homOfLE hbc)) x.val).symm)) m s
  let hc {a b : ℕ} (f : a ⟶ b) :
      boundarySectionsMap A π n h f (t b) = t a := congrArg Subtype.val (ht a b (leOfHom f))
  let z := compatibleOfStages A π n h (fun a ↦ (t a).val) hc
  have hz : z ∈ compatibleSectionDegree A π n h d := by
    intro a
    rw [show z = compatibleOfStages A π n h (fun a ↦ (t a).val) hc from rfl,
      compatibleEval_ofStages]
    exact (t a).property
  refine ⟨⟨z, hz⟩, ?_⟩
  exact (compatibleEval_ofStages A π n h _ hc m).trans (congrArg Subtype.val htm)

include hne hgen in
/-- Actual positive homogeneous sections are attained by evaluation of the graded algebra. -/
theorem compatibleGradedEval_uniformLifting : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : grade (boundaryLine A π m n h) ⊤ d,
      ∃ t : CompatibleGradedSections A π n h, compatibleGradedEval A π n h m t = s := by
  obtain ⟨N, hN⟩ := compatibleDegree_uniformLifting A π n h hne hgen
  refine ⟨N, fun d hd m s ↦ ?_⟩
  obtain ⟨t, ht⟩ := hN d hd m s
  exact ⟨DirectSum.of _ d t, (compatibleGradedEval_of A π n h m d t).trans ht⟩

end FLT.Mazur.PolygonArithmeticStages
