/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineNeighborhoodStability
public import FLT.Mazur.FiniteGroupInvariantAffineCover

/-!
# Finite invariant affine covers from actual finite-set neighborhoods

Intersect translates of a common affine neighborhood of each finite orbit.
Quasi-compactness selects finitely many of these actual invariant charts. Every
selected chart retains the restricted group action and affine invariant overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupNeighborhoodCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {G : Type} [Group G] [Finite G] {X : Scheme} [X.IsSeparated]
  (ρ : G →* Aut X) (hX : FiniteAffineNeighborhood.HasNeighborhoods X)

include hX in
/-- Finite-set neighborhoods give invariant affine neighborhoods of each orbit. -/
theorem exists_chart (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by
  obtain ⟨V, hV, hVs⟩ := hX (Set.range fun g : G => (ρ g).hom x) (Set.finite_range _)
  refine ⟨FiniteGroupNeighborhood.invariantCore ρ V,
    FiniteGroupNeighborhood.isAffineOpen_invariantCore ρ V hV, ?_,
    FiniteGroupNeighborhood.invariantCore_preimage ρ V⟩
  exact (FiniteGroupNeighborhood.mem_invariantCore ρ V x).mpr
    (fun g => hVs ⟨g, rfl⟩)

/-- A chosen actual invariant affine neighborhood of each point. -/
def chart (x : X) : X.Opens := (exists_chart ρ hX x).choose

/-- Each chart is affine. -/
theorem chart_affine (x : X) : IsAffineOpen (chart ρ hX x) :=
  (exists_chart ρ hX x).choose_spec.1

/-- Each chart contains its defining point. -/
theorem mem_chart (x : X) : x ∈ chart ρ hX x :=
  (exists_chart ρ hX x).choose_spec.2.1

/-- Each chart is stable under every original group element. -/
theorem chart_stable (x : X) (g : G) :
    (ρ g).hom ⁻¹ᵁ chart ρ hX x = chart ρ hX x :=
  (exists_chart ρ hX x).choose_spec.2.2 g

/-- The constructed invariant charts cover the original scheme. -/
theorem iSup_chart : ⨆ x, chart ρ hX x = ⊤ := by
  apply top_le_iff.mp
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, mem_chart ρ hX x⟩

/-- The invariant affine open cover before selecting finitely many charts. -/
def cover : X.OpenCover :=
  X.openCoverOfIsOpenCover (chart ρ hX) (iSup_chart ρ hX)

/-- The action on every chart is the restriction of the original action. -/
def chartAction (x : X) : G →* Aut (chart ρ hX x).toScheme :=
  FiniteGroupRestriction.restrictedAction ρ _ (chart_stable ρ hX x)

/-- Chart inclusions are equivariant, as actual scheme morphisms. -/
@[reassoc] theorem chartAction_inclusion (x : X) (g : G) :
    (chartAction ρ hX x g).hom ≫ (chart ρ hX x).ι =
      (chart ρ hX x).ι ≫ (ρ g).hom :=
  FiniteGroupRestriction.restrictedAction_hom_ι _ _ _ g

/-- Intersections of invariant charts remain affine. -/
theorem overlap_affine (x y : X) : IsAffineOpen (chart ρ hX x ⊓ chart ρ hX y) :=
  (chart_affine ρ hX x).inf (chart_affine ρ hX y)

/-- Intersections of invariant charts remain invariant. -/
theorem overlap_stable (x y : X) (g : G) :
    (ρ g).hom ⁻¹ᵁ (chart ρ hX x ⊓ chart ρ hX y) = chart ρ hX x ⊓ chart ρ hX y := by
  change (ρ g).hom ⁻¹ᵁ chart ρ hX x ⊓ (ρ g).hom ⁻¹ᵁ chart ρ hX y = _
  rw [chart_stable, chart_stable]

variable [CompactSpace X]

/-- A finite selection of the constructed invariant affine charts. -/
def finiteCover : X.OpenCover := (cover ρ hX).finiteSubcover

/-- The constructed invariant cover has finitely many chart indices. -/
instance finiteCoverFintype : Fintype (finiteCover ρ hX).I₀ := by
  unfold finiteCover
  infer_instance

/-- Each selected chart is one of the original affine neighborhoods. -/
instance finiteCover_isAffine (i : (finiteCover ρ hX).I₀) :
    IsAffine ((finiteCover ρ hX).X i) :=
  chart_affine ρ hX ((cover ρ hX).idx i.val)

/-- Every selected chart still carries the original group action. -/
def finiteAction (i : (finiteCover ρ hX).I₀) : G →* Aut ((finiteCover ρ hX).X i) :=
  chartAction ρ hX ((cover ρ hX).idx i.val)

/-- The finite cover inclusions retain exact equivariance. -/
@[reassoc] theorem finiteAction_inclusion (i : (finiteCover ρ hX).I₀) (g : G) :
    (finiteAction ρ hX i g).hom ≫ (finiteCover ρ hX).f i =
      (finiteCover ρ hX).f i ≫ (ρ g).hom :=
  chartAction_inclusion ρ hX ((cover ρ hX).idx i.val) g

end FLT.Mazur.FiniteGroupNeighborhoodCover
