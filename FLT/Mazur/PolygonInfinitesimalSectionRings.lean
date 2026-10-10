/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalLineCoherence
public import FLT.Mazur.SectionGradedIsoRing
public import FLT.Mazur.SectionGradedPullbackRing

/-!
# Actual section-ring transitions of the infinitesimal polygons

The coefficient restriction and the specified boundary-line comparison
induce degree-preserving maps of the entire section rings. These maps do
not assume that reduction is flat or that sections lift across reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n)

/-- All tensor degrees of the actual ample boundary line at a concrete stage. -/
abbrev boundaryGradedSections (m : ℕ) := SectionGradedSum.Sections (boundaryLine R m n h) ⊤

/-- The boundary-line rank-one theorem supplies the commutative section-ring structure. -/
instance boundaryLine_rankOne_fact (m : ℕ) : Fact (LocallyFreeRankOne (boundaryLine R m n h)) :=
  ⟨boundaryLine_rankOne R m n h⟩

/-- Every actual stage section ring is commutative. -/
instance boundaryGradedSectionsCommRing (m : ℕ) : CommRing (boundaryGradedSections R n h m) :=
  inferInstanceAs (CommRing (SectionGradedSum.Sections (boundaryLine R m n h) ⊤))

/-- The actual stage transition pulls all sections back and then compares boundary lines. -/
def boundarySectionsMap {a b : ℕ} (f : a ⟶ b) :
    boundaryGradedSections R n h b →+* boundaryGradedSections R n h a :=
  (SectionGradedIso.ringHom (boundaryLineSystemIso R n h f) ⊤).comp
    (SectionGradedPullback.ringHom ((stageSystem R n h).map f) (boundaryLine R b n h))

/-- Each homogeneous component is the actual tensor-power pullback and line comparison. -/
theorem boundarySectionsMap_of {a b : ℕ} (f : a ⟶ b) (k : ℕ)
    (s : Piece (boundaryLine R b n h) ⊤ k) :
    boundarySectionsMap R n h f (of (boundaryLine R b n h) ⊤ k s) =
      of (boundaryLine R a n h) ⊤ k
        (SectionGradedIso.pieceMap (boundaryLineSystemIso R n h f) k ⊤
          (SectionGradedPullback.pull ((stageSystem R n h).map f)
            (boundaryLine R b n h) k ⊤ s)) := by
  rw [boundarySectionsMap, RingHom.comp_apply]
  change SectionGradedIso.sumMap (boundaryLineSystemIso R n h f) ⊤
    (SectionGradedPullback.sumMap ((stageSystem R n h).map f) (boundaryLine R b n h)
      (of (boundaryLine R b n h) ⊤ k s)) = _
  rw [SectionGradedPullback.sumMap_of, SectionGradedIso.sumMap_of]
  rfl

/-- Restriction preserves every actual homogeneous submodule, including degree zero. -/
theorem boundarySectionsMap_mem_grade {a b : ℕ} (f : a ⟶ b) {k : ℕ}
    {s : boundaryGradedSections R n h b} (hs : s ∈ grade (boundaryLine R b n h) ⊤ k) :
    boundarySectionsMap R n h f s ∈ grade (boundaryLine R a n h) ⊤ k := by
  obtain ⟨t, rfl⟩ := hs
  exact ⟨_, (boundarySectionsMap_of R n h f k t).symm⟩

/-- The adjacent section-ring transitions define an actual inverse system of rings. -/
def boundarySectionRingSystem : ℕᵒᵖ ⥤ CommRingCat :=
  Functor.ofOpSequence (X := fun m ↦ CommRingCat.of (boundaryGradedSections R n h m))
    (fun m ↦ CommRingCat.ofHom
    (boundarySectionsMap R n h (homOfLE (Nat.le_succ m))))

end FLT.Mazur.PolygonInfinitesimalStages
