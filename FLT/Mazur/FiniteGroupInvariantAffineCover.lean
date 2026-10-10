/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupAffineNeighborhood
public import FLT.Mazur.FiniteGroupOpenRestriction

/-!
# An actual cover by invariant affine charts

Choose the proved neighborhoods, construct their open cover, and retain the
restricted group action on each chart. Intersections remain invariant and affine.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupInvariantCover

variable {G : Type*} [Group G] [Finite G] {X : Scheme} [X.IsSeparated]
variable (ρ : G →* Aut X) (L : X.Modules) [Fact (FCurve.LocallyFreeRankOne L)]
variable (hL : FCurve.AmpleLineBundle L)

/-- A chosen invariant affine neighborhood of each point, obtained from ampleness. -/
def chart (x : X) : X.Opens :=
  (FiniteGroupNeighborhood.exists_invariant_affine ρ L hL x).choose

/-- Every chosen chart is affine. -/
lemma chart_affine (x : X) : IsAffineOpen (chart ρ L hL x) :=
  (FiniteGroupNeighborhood.exists_invariant_affine ρ L hL x).choose_spec.1

/-- The point defining a chart belongs to that chart. -/
lemma mem_chart (x : X) : x ∈ chart ρ L hL x :=
  (FiniteGroupNeighborhood.exists_invariant_affine ρ L hL x).choose_spec.2.1

/-- The chosen charts are invariant under the actual scheme action. -/
lemma chart_stable (x : X) (g : G) :
    (ρ g).hom ⁻¹ᵁ chart ρ L hL x = chart ρ L hL x :=
  (FiniteGroupNeighborhood.exists_invariant_affine ρ L hL x).choose_spec.2.2 g

/-- The chosen invariant affine opens cover the original scheme. -/
lemma iSup_chart : ⨆ x, chart ρ L hL x = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, mem_chart ρ L hL x⟩

/-- The actual scheme open cover used to glue finite-group quotients. -/
def cover : X.OpenCover :=
  X.openCoverOfIsOpenCover (chart ρ L hL) (iSup_chart ρ L hL)

/-- The actual restricted action on each member of the cover. -/
def chartAction (x : X) : G →* Aut (chart ρ L hL x).toScheme :=
  FiniteGroupRestriction.restrictedAction ρ _ (chart_stable ρ L hL x)

/-- Pairwise overlaps of the chosen charts are affine. -/
lemma overlap_affine (x y : X) :
    IsAffineOpen (chart ρ L hL x ⊓ chart ρ L hL y) :=
  (chart_affine ρ L hL x).inf (chart_affine ρ L hL y)

/-- Pairwise overlaps retain the group action. -/
lemma overlap_stable (x y : X) (g : G) :
    (ρ g).hom ⁻¹ᵁ (chart ρ L hL x ⊓ chart ρ L hL y) =
      chart ρ L hL x ⊓ chart ρ L hL y := by
  change (ρ g).hom ⁻¹ᵁ chart ρ L hL x ⊓ (ρ g).hom ⁻¹ᵁ chart ρ L hL y = _
  rw [chart_stable, chart_stable]

end FLT.Mazur.FiniteGroupInvariantCover
