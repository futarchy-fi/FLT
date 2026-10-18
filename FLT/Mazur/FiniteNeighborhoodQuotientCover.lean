/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupNeighborhoodAffineCover
public import FLT.Mazur.StableAffineQuotientCartesian
public import FLT.Mazur.StableAffineQuotientDescent

/-!
# Finite quotient covers from finite-set affine neighborhoods

The chosen finite invariant cover embeds in the existing quotient diagram.
Its actual affine quotients cover the glued scheme, and each source chart
is the scheme pullback of its quotient chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient FLT.Mazur.StableAffineQuotient
namespace FLT.Mazur.FiniteGroupNeighborhoodCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {G : Type} [Group G] [Finite G] {X : Scheme} [X.IsSeparated]
  (ρ : G →* Aut X) (hX : FiniteAffineNeighborhood.HasNeighborhoods X)

/-- Every constructed neighborhood is an object of the actual quotient diagram. -/
def stableChart (x : X) : StableAffineQuotient.Chart ρ :=
  ⟨chart ρ hX x, chart_affine ρ hX x, chart_stable ρ hX x⟩

include hX in
/-- Finite-set neighborhoods supply the coverage needed by global quotient gluing. -/
theorem stableCharts_cover : ⨆ U : StableAffineQuotient.Chart ρ, U.val = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨stableChart ρ hX x, mem_chart ρ hX x⟩

/-- The global quotient map constructed from the actual neighborhood cover. -/
def quotientMap : X ⟶ glued ρ := StableAffineQuotient.map ρ (stableCharts_cover ρ hX)

/-- The constructed quotient is integral. -/
instance quotientMap_integral : IsIntegralHom (quotientMap ρ hX) := by
  unfold quotientMap
  infer_instance

/-- The constructed quotient is surjective. -/
instance quotientMap_surjective : Surjective (quotientMap ρ hX) := by
  unfold quotientMap
  infer_instance

/-- The global quotient is invariant for the original scheme action. -/
@[reassoc] theorem quotientMap_invariant (g : G) :
    (ρ g).hom ≫ quotientMap ρ hX = quotientMap ρ hX :=
  map_invariant ρ (stableCharts_cover ρ hX) g

/-- Its point fibers are exactly the original group orbits. -/
theorem quotientMap_eq_iff_orbit (x y : X) :
    quotientMap ρ hX x = quotientMap ρ hX y ↔ ∃ g : G, y = (ρ g).hom x :=
  map_eq_iff_orbit ρ (stableCharts_cover ρ hX) x y

/-- Every invariant scheme map factors uniquely through this constructed quotient. -/
theorem quotientMap_existsUnique_desc {Y : Scheme} (f : X ⟶ Y)
    (hf : ∀ g : G, (ρ g).hom ≫ f = f) :
    ∃! k : glued ρ ⟶ Y, quotientMap ρ hX ≫ k = f :=
  StableAffineQuotient.existsUnique_desc ρ (stableCharts_cover ρ hX) f hf

variable [CompactSpace X]

/-- The selected finite chart as an object of the invariant quotient diagram. -/
def finiteStableChart (i : (finiteCover ρ hX).I₀) : StableAffineQuotient.Chart ρ :=
  stableChart ρ hX ((cover ρ hX).idx i.val)

/-- The original selected chart quotient maps into the actual global quotient. -/
def finiteQuotientInclusion (i : (finiteCover ρ hX).I₀) :
    quotient (finiteAction ρ hX i) ⟶ glued ρ := chartMap ρ (finiteStableChart ρ hX i)

/-- Each selected quotient inclusion is an open immersion. -/
instance finiteQuotientInclusion_isOpenImmersion (i : (finiteCover ρ hX).I₀) :
    IsOpenImmersion (finiteQuotientInclusion ρ hX i) := by
  unfold finiteQuotientInclusion
  infer_instance

/-- The selected chart square commutes on the full schemes. -/
@[reassoc] theorem finiteQuotientInclusion_fac (i : (finiteCover ρ hX).I₀) :
    SchemeFiniteGroupQuotient.quotientMap (finiteAction ρ hX i) ≫
      finiteQuotientInclusion ρ hX i = (finiteCover ρ hX).f i ≫ quotientMap ρ hX :=
  (ι_map ρ (stableCharts_cover ρ hX) (finiteStableChart ρ hX i)).symm

/-- The selected chart square is cartesian, including its structure sheaves. -/
theorem finiteQuotientInclusion_isPullback (i : (finiteCover ρ hX).I₀) :
    IsPullback ((finiteCover ρ hX).f i)
      (SchemeFiniteGroupQuotient.quotientMap (finiteAction ρ hX i))
      (quotientMap ρ hX) (finiteQuotientInclusion ρ hX i) :=
  chart_isPullback ρ (stableCharts_cover ρ hX) (finiteStableChart ρ hX i)

/-- The original finite selection also covers the actual quotient scheme. -/
def finiteQuotientCover : (glued ρ).OpenCover where
  I₀ := (finiteCover ρ hX).I₀
  X i := quotient (finiteAction ρ hX i)
  f i := finiteQuotientInclusion ρ hX i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    obtain ⟨x, rfl⟩ := (quotientMap ρ hX).surjective z
    obtain ⟨i, y, rfl⟩ := (finiteCover ρ hX).exists_eq x
    refine ⟨i, SchemeFiniteGroupQuotient.quotientMap (finiteAction ρ hX i) y, ?_⟩
    exact congrArg (fun f ↦ f y) (finiteQuotientInclusion_fac ρ hX i)

/-- This quotient cover has finitely many charts. -/
instance finiteQuotientCoverFintype : Fintype (finiteQuotientCover ρ hX).I₀ :=
  inferInstanceAs (Fintype (finiteCover ρ hX).I₀)

end FLT.Mazur.FiniteGroupNeighborhoodCover
