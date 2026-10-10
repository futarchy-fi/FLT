/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryUniformLifting
public import FLT.Mazur.PolygonCompatibleSectionReduction
public import FLT.Mazur.SurjectiveTowerLifting

/-!
# Lifting actual homogeneous sections to compatible formal sections

The uniform adjacent lifting theorem extends every sufficiently positive
homogeneous section to a compatible homogeneous section across all stages.
The resulting element belongs to the already constructed graded algebra.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

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

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- Restriction on the actual homogeneous submodule of a fixed degree. -/
def boundaryDegreeTransition (d : ℕ) {a b : ℕ} (hab : a ≤ b) :
    grade (boundaryLine K b n h) ⊤ d → grade (boundaryLine K a n h) ⊤ d :=
  fun s ↦ ⟨boundarySectionsMap K n h (homOfLE hab) s,
    boundarySectionsMap_mem_grade K n h (homOfLE hab) s.property⟩

/-- The adjacent ring map is the specified tensor-degree section map. -/
theorem boundarySectionsMap_adjacent_of (m d : ℕ)
    (s : Piece (boundaryLine K (m + 1) n h) ⊤ d) :
    boundarySectionsMap K n h (homOfLE (Nat.le_succ m))
      (of (boundaryLine K (m + 1) n h) ⊤ d s) =
    of (boundaryLine K m n h) ⊤ d
      (SectionGradedLinePullback.sectionMap (stageRestriction K m n h)
        (adjacentBoundaryLineIso K m n h) d ⊤ s) := by
  have hf : (stageSystem K n h).map (homOfLE (Nat.le_succ m)) =
      stageRestriction K m n h := Functor.ofSequence_map_homOfLE_succ _ m
  have he : ((Scheme.Modules.pullback
      ((stageSystem K n h).map (homOfLE (Nat.le_succ m)))).obj
        (boundaryLine K (m + 1) n h) ≅ boundaryLine K m n h) =
      ((Scheme.Modules.pullback (stageRestriction K m n h)).obj
        (boundaryLine K (m + 1) n h) ≅ boundaryLine K m n h) := by rw [hf]
  exact (SectionGradedLinePullback.ringHom_of _
    (boundaryLineSystemIso K n h (homOfLE (Nat.le_succ m))) d s).trans
      (congrArg (of (boundaryLine K m n h) ⊤ d)
        (boundarySectionMap_transport hf he _ d s))

/-- Adjacent section lifting is surjectivity on the original homogeneous submodule. -/
theorem boundaryDegreeTransition_surjective (m d : ℕ)
    (hs : Function.Surjective
      (SectionGradedLinePullback.sectionMap (stageRestriction K m n h)
        (adjacentBoundaryLineIso K m n h) d ⊤)) :
    Function.Surjective (boundaryDegreeTransition K n h d (Nat.le_succ m)) := by
  intro s
  obtain ⟨t, ht⟩ := s.property
  obtain ⟨u, hu⟩ := hs t
  refine ⟨⟨of (boundaryLine K (m + 1) n h) ⊤ d u, ⟨u, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact (boundarySectionsMap_adjacent_of K n h m d u).trans
    ((congrArg (of (boundaryLine K m n h) ⊤ d) hu).trans ht)

variable [NeZero n]

/-- Every sufficiently positive stage section lifts to the constructed compatible degree. -/
theorem compatibleDegree_uniformLifting : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : grade (boundaryLine K m n h) ⊤ d,
      ∃ t : compatibleSectionDegree K n h d, compatibleEval K n h m t = s := by
  obtain ⟨N, hN⟩ := boundarySections_uniformSurjective K n h
  refine ⟨N, fun d hd m s ↦ ?_⟩
  obtain ⟨t, ht, htm⟩ := SurjectiveTowerLifting.exists_compatible
    (boundaryDegreeTransition K n h d)
    (fun a ↦ boundaryDegreeTransition_surjective K n h a d (hN d hd a))
    (fun a x ↦ Subtype.ext (by
      change boundarySectionsMap K n h (𝟙 a) x = x
      rw [boundarySectionsMap_id]; rfl))
    (fun hab hbc x ↦ Subtype.ext (by
      change boundarySectionsMap K n h (homOfLE hab)
        (boundarySectionsMap K n h (homOfLE hbc) x) = _
      exact (DFunLike.congr_fun (boundarySectionsMap_comp K n h
        (homOfLE hab) (homOfLE hbc)) x.val).symm)) m s
  let hc {a b : ℕ} (f : a ⟶ b) :
      boundarySectionsMap K n h f (t b) = t a := congrArg Subtype.val (ht a b (leOfHom f))
  let z := compatibleOfStages K n h (fun a ↦ (t a).val) hc
  have hz : z ∈ compatibleSectionDegree K n h d := by
    intro a
    rw [show z = compatibleOfStages K n h (fun a ↦ (t a).val) hc from rfl,
      compatibleEval_ofStages]
    exact (t a).property
  refine ⟨⟨z, hz⟩, ?_⟩
  exact (compatibleEval_ofStages K n h _ hc m).trans (congrArg Subtype.val htm)

/-- Actual positive homogeneous sections are attained by evaluation of the graded algebra. -/
theorem compatibleGradedEval_uniformLifting : ∃ N : ℕ, ∀ d ≥ N, ∀ m : ℕ,
    ∀ s : grade (boundaryLine K m n h) ⊤ d,
      ∃ t : CompatibleGradedSections K n h, compatibleGradedEval K n h m t = s := by
  obtain ⟨N, hN⟩ := compatibleDegree_uniformLifting K n h
  refine ⟨N, fun d hd m s ↦ ?_⟩
  obtain ⟨t, ht⟩ := hN d hd m s
  exact ⟨DirectSum.of _ d t, (compatibleGradedEval_of K n h m d t).trans ht⟩

end FLT.Mazur.PolygonInfinitesimalStages
