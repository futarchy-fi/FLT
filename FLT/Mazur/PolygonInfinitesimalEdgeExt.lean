/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchExt
public import FLT.Mazur.PolygonInfinitesimalEdgeCoordinates

/-!
# Full Laurent edges detect maps from the whole infinitesimal polygon

Each arithmetic node is detected by its two punctured branches. The cyclic
overlap equations identify those branches with neighboring full Laurent
edges, so equality on all edges retains every original node and nilpotent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- Separated-target maps from the whole nonreduced polygon agree if all full edges agree. -/
theorem edge_hom_ext {Y S : Scheme} (s : Y ⟶ S) [IsSeparated s]
    (f g : scheme R t n h ⟶ Y) (hb : f ≫ s = g ≫ s)
    (he : ∀ i, edge R t n h i ≫ f = edge R t n h i ≫ g) : f = g := by
  apply chart_hom_ext R t n h
  intro i
  apply branch_hom_ext t s
  · simpa only [Category.assoc] using congrArg (chart R t n h i ≫ ·) hb
  · exact (Category.assoc _ _ _).symm.trans ((he i).trans (Category.assoc _ _ _))
  · rw [← cancel_epi (edgeInversion R).hom]
    have ho : precedingBranch R t ≫ chart R t n h i =
        edge R t n h (finRotate n i) := by
      simpa only [Equiv.symm_apply_apply, edge] using
        (overlap R t n h (finRotate n i)).symm
    have hx := he (finRotate n i)
    rw [← ho] at hx
    simpa only [precedingBranch, Category.assoc] using hx

end FLT.Mazur.PolygonInfinitesimal
