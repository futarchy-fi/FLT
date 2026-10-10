/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientMap
public import FLT.Mazur.FiniteGroupInvariantAffineCover

/-!
# A global finite-group quotient for schemes with an ample line bundle

Ampleness supplies the invariant affine cover, so the global quotient map
is constructed without assuming an atlas or any overlap comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (L : X.Modules) [Fact (FCurve.LocallyFreeRankOne L)]
variable (hL : FCurve.AmpleLineBundle L)

/-- The previously constructed ample neighborhoods are objects of the actual quotient diagram. -/
def ampleChart (x : X) : Chart ρ :=
  ⟨FiniteGroupInvariantCover.chart ρ L hL x,
    FiniteGroupInvariantCover.chart_affine ρ L hL x,
    FiniteGroupInvariantCover.chart_stable ρ L hL x⟩

include hL in
/-- Ampleness proves that the invariant affine chart diagram covers the original scheme. -/
theorem ample_charts_cover : ⨆ U : Chart ρ, U.val = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨ampleChart ρ L hL x, FiniteGroupInvariantCover.mem_chart ρ L hL x⟩

/-- The constructed global morphism from an ample separated scheme to its finite-group quotient. -/
def ampleMap : X ⟶ glued ρ := map ρ (ample_charts_cover ρ L hL)

/-- Every invariant affine chart has the prescribed quotient map after gluing. -/
@[reassoc]
lemma ι_ampleMap (U : Chart ρ) : U.val.ι ≫ ampleMap ρ L hL = localMap ρ U :=
  ι_map ρ (ample_charts_cover ρ L hL) U

/-- The actual global ample quotient morphism is invariant. -/
@[reassoc]
lemma ampleMap_invariant (g : G) : (ρ g).hom ≫ ampleMap ρ L hL = ampleMap ρ L hL :=
  map_invariant ρ (ample_charts_cover ρ L hL) g

/-- The actual global ample quotient morphism is surjective. -/
theorem ampleMap_surjective : Function.Surjective (ampleMap ρ L hL) :=
  map_surjective ρ (ample_charts_cover ρ L hL)

end FLT.Mazur.StableAffineQuotient
