/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientNeighborhood
public import FLT.Mazur.StableAffineQuotientChartIntersection
public import FLT.Mazur.StableAffineQuotientAffineDescent

/-!
# Local descent into affine target neighborhoods

Pairs of a stable affine source chart and an affine target open containing
its image form covers of both the source and quotient. The invariant-ring
universal property constructs the local descents, and their compatibility
is proved on actual scheme overlaps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] {X Y : Scheme.{u}}
variable (ρ : G →* Aut X) (f : X ⟶ Y)

/-- Source and target affine neighborhoods, with only geometric containment as data. -/
abbrev DescentChart :=
  {p : Chart ρ × Y.affineOpens // p.1.val ≤ f ⁻¹ᵁ p.2.val}

variable (hf : ∀ g : G, (ρ g).hom ≫ f = f)

include hf in
/-- The restriction to an affine target neighborhood is invariant as a scheme morphism. -/
lemma descentChart_invariant (c : DescentChart ρ f) (g : G) :
    (action ρ c.val.1 g).hom ≫ f.resLE c.val.2.val c.val.1.val c.property =
      f.resLE c.val.2.val c.val.1.val c.property := by
  rw [← cancel_mono c.val.2.val.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
    chart_invariant ρ f hf]

/-- The local invariant map descends to its chosen affine target open, then to the target. -/
def targetLocalDesc (c : DescentChart ρ f) : quotient (action ρ c.val.1) ⟶ Y := by
  let _ : IsAffine c.val.2.val.toScheme := c.val.2.property
  exact (existsUnique_affine_desc (action ρ c.val.1)
    (f.resLE c.val.2.val c.val.1.val c.property)
    (descentChart_invariant ρ f hf c)).choose ≫ c.val.2.val.ι

/-- Each constructed local map factors the original map on its source chart. -/
@[reassoc]
lemma targetLocalDesc_fac (c : DescentChart ρ f) :
    quotientMap (action ρ c.val.1) ≫ targetLocalDesc ρ f hf c = c.val.1.val.ι ≫ f := by
  let _ : IsAffine c.val.2.val.toScheme := c.val.2.property
  unfold targetLocalDesc
  rw [← Category.assoc,
    (existsUnique_affine_desc (action ρ c.val.1)
      (f.resLE c.val.2.val c.val.1.val c.property)
      (descentChart_invariant ρ f hf c)).choose_spec.1, Scheme.Hom.resLE_comp_ι]

variable [Finite G] [X.IsSeparated]

/-- The local affine-target constructions agree as scheme morphisms on every overlap. -/
lemma targetLocalDesc_compatible (c d : DescentChart ρ f) :
    pullback.fst (chartMap ρ c.val.1) (chartMap ρ d.val.1) ≫ targetLocalDesc ρ f hf c =
      pullback.snd (chartMap ρ c.val.1) (chartMap ρ d.val.1) ≫ targetLocalDesc ρ f hf d :=
  localDesc_compatible ρ c.val.1 d.val.1 f _ _
    (targetLocalDesc_fac ρ f hf c) (targetLocalDesc_fac ρ f hf d)

variable (hcover : ⨆ U : Chart ρ, U.val = ⊤)

include hf hcover in
omit [X.IsSeparated] in
/-- The source charts adapted to affine target opens cover the entire original scheme. -/
lemma descentCharts_cover : ⨆ c : DescentChart ρ f, c.val.1.val = ⊤ := by
  apply top_le_iff.mp
  intro x _
  obtain ⟨U, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ U : Chart ρ, U.val from hcover.symm ▸ trivial)
  obtain ⟨W, V, hxW, hV, hWV⟩ := exists_chart_affine_target ρ f hf U x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, ⟨V, hV⟩⟩, hWV⟩, hxW⟩

/-- The actual source cover by charts adapted to affine target neighborhoods. -/
def descentSourceCover : X.OpenCover :=
  X.openCoverOfIsOpenCover (fun c : DescentChart ρ f ↦ c.val.1.val)
    (descentCharts_cover ρ f hf hcover)

/-- The actual quotient cover on which the local affine-target descents are defined. -/
def descentQuotientCover : (glued ρ).OpenCover where
  I₀ := DescentChart ρ f
  X c := quotient (action ρ c.val.1)
  f c := chartMap ρ c.val.1
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨x, rfl⟩ := map_surjective ρ hcover z
    obtain ⟨c, a, rfl⟩ := (descentSourceCover ρ f hf hcover).exists_eq x
    refine ⟨c, quotientMap (action ρ c.val.1) a, ?_⟩
    exact (map_apply_chart ρ hcover c.val.1 a).symm

end FLT.Mazur.StableAffineQuotient
