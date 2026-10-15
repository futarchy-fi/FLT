/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLineCoherence
public import FLT.Mazur.SectionGradedIsoRing
public import FLT.Mazur.SectionGradedPullbackRing

/-!
# Actual section-ring transitions of the arithmetic polygons

The coefficient restriction and the specified boundary-line comparison
induce degree-preserving maps of the entire section rings. These maps do
not assume that reduction is flat or that sections lift across reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- All tensor degrees of the actual ample boundary line at a concrete stage. -/
abbrev boundaryGradedSections (m : ℕ) := SectionGradedSum.Sections (boundaryLine A π m n h) ⊤

/-- The boundary-line rank-one theorem supplies the commutative section-ring structure. -/
instance boundaryLine_rankOne_fact (m : ℕ) : Fact (LocallyFreeRankOne (boundaryLine A π m n h)) :=
  ⟨boundaryLine_rankOne A π m n h⟩

/-- Every actual stage section ring is commutative. -/
instance boundaryGradedSectionsCommRing (m : ℕ) : CommRing (boundaryGradedSections A π n h m) :=
  inferInstanceAs (CommRing (SectionGradedSum.Sections (boundaryLine A π m n h) ⊤))

/-- The actual stage transition pulls all sections back and then compares boundary lines. -/
def boundarySectionsMap {a b : ℕ} (f : a ⟶ b) :
    boundaryGradedSections A π n h b →+* boundaryGradedSections A π n h a :=
  (SectionGradedIso.ringHom (boundaryLineSystemIso A π n h f) ⊤).comp
    (SectionGradedPullback.ringHom ((stageSystem A π n h).map f) (boundaryLine A π b n h))

/-- Each homogeneous component is the actual tensor-power pullback and line comparison. -/
theorem boundarySectionsMap_of {a b : ℕ} (f : a ⟶ b) (k : ℕ)
    (s : Piece (boundaryLine A π b n h) ⊤ k) :
    boundarySectionsMap A π n h f (of (boundaryLine A π b n h) ⊤ k s) =
      of (boundaryLine A π a n h) ⊤ k
        (SectionGradedIso.pieceMap (boundaryLineSystemIso A π n h f) k ⊤
          (SectionGradedPullback.pull ((stageSystem A π n h).map f)
            (boundaryLine A π b n h) k ⊤ s)) := by
  rw [boundarySectionsMap, RingHom.comp_apply]
  change SectionGradedIso.sumMap (boundaryLineSystemIso A π n h f) ⊤
    (SectionGradedPullback.sumMap ((stageSystem A π n h).map f) (boundaryLine A π b n h)
      (of (boundaryLine A π b n h) ⊤ k s)) = _
  rw [SectionGradedPullback.sumMap_of, SectionGradedIso.sumMap_of]
  rfl

/-- Restriction preserves every actual homogeneous submodule, including degree zero. -/
theorem boundarySectionsMap_mem_grade {a b : ℕ} (f : a ⟶ b) {k : ℕ}
    {s : boundaryGradedSections A π n h b} (hs : s ∈ grade (boundaryLine A π b n h) ⊤ k) :
    boundarySectionsMap A π n h f s ∈ grade (boundaryLine A π a n h) ⊤ k := by
  obtain ⟨t, rfl⟩ := hs
  exact ⟨_, (boundarySectionsMap_of A π n h f k t).symm⟩

/-- The adjacent section-ring transitions define an actual inverse system of rings. -/
def boundarySectionRingSystem : ℕᵒᵖ ⥤ CommRingCat :=
  Functor.ofOpSequence (X := fun m ↦ CommRingCat.of (boundaryGradedSections A π n h m))
    (fun m ↦ CommRingCat.ofHom
    (boundarySectionsMap A π n h (homOfLE (Nat.le_succ m))))

end FLT.Mazur.PolygonArithmeticStages
