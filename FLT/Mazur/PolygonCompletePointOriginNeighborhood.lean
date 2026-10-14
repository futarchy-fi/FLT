/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicChartSquare
public import FLT.Mazur.WeierstrassOriginNeighborhoodCover

/-!
# The original complete-base preimage of the cubic parameter neighborhood

Pull back the concrete origin neighborhood along the actual pointed proper morphism.
The result contains the original marking and covers the source together with its
original Cartier complement. The neighborhood is not assumed affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "s" => completeBaseMarking K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- The actual open inverse image of the original cubic parameter neighborhood. -/
def completePointOriginOpen : (exactVeroneseProj K n h).Opens :=
  (g) ⁻¹ᵁ (originNeighborhoodInclusion (W)).opensRange

local notation "V" => completePointOriginOpen K n h i

/-- The restricted original cubic morphism, with the actual parameter neighborhood as target. -/
def completePointToOrigin : (V).toScheme ⟶ Spec (.of (OriginNeighborhood (W))) :=
  IsOpenImmersion.lift (originNeighborhoodInclusion (W)) ((V).ι ≫ (g)) (by
    rintro _ ⟨x, rfl⟩
    exact x.property)

/-- Restriction retains the entire original cubic map. -/
@[reassoc] theorem completePointToOrigin_inclusion :
    completePointToOrigin K n h i ≫ originNeighborhoodInclusion (W) = (V).ι ≫ (g) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The parameter-neighborhood square is the actual Cartesian inverse image. -/
theorem completePointToOrigin_isPullback :
    IsPullback (completePointToOrigin K n h i) (V).ι
      (originNeighborhoodInclusion (W)) (g) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (completePointToOrigin_inclusion K n h i).symm
  rw [Scheme.Opens.opensRange_ι]
  rfl

/-- The original restricted map is proper, including on the collapsed fiber. -/
theorem completePointToOrigin_proper : IsProper (completePointToOrigin K n h i) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact MorphismProperty.of_isPullback
    (completePointToOrigin_isPullback K n h i).flip inferInstance

/-- The whole original marking lies in the actual inverse-image neighborhood. -/
theorem completePointMarking_preimage_origin : (s) ⁻¹ᵁ (V) = ⊤ := by
  apply top_unique
  intro x _
  change ((s) ≫ (g)) x ∈ Set.range (originNeighborhoodInclusion (W))
  rw [completePointToIntegralCubic_marking, ← originNeighborhoodSection_inclusion]
  exact ⟨((S₀).toSpecΓ ≫ originNeighborhoodSection (W)) x, rfl⟩

/-- The actual parameter preimage and original marked-point complement cover the family. -/
theorem completePointOriginOpen_complement_cover : (V) ⊔ (s).ker.support.compl = ⊤ := by
  apply top_unique
  intro x _
  rcases originNeighborhood_affine_cover (W) ((g) x) with hx | hx
  · exact Or.inl hx
  · right
    have he := completePointToIntegralCubic_preimage_z K n h i
    rw [← he]
    exact hx

/-- The actual original marking lifted to the parameter inverse image. -/
def completePointMarkingOrigin : S₀ ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι (s) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (show x ∈ (s) ⁻¹ᵁ (V) from by
      rw [completePointMarking_preimage_origin]; trivial))

/-- The neighborhood marking retains the original section. -/
@[reassoc] theorem completePointMarkingOrigin_inclusion :
    completePointMarkingOrigin K n h i ≫ (V).ι = (s) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual neighborhood marking maps to the original parameter-ring augmentation. -/
@[reassoc] theorem completePointMarkingOrigin_toOrigin :
    completePointMarkingOrigin K n h i ≫ completePointToOrigin K n h i =
      (S₀).toSpecΓ ≫ originNeighborhoodSection (W) := by
  apply (cancel_mono (originNeighborhoodInclusion (W))).mp
  rw [Category.assoc, completePointToOrigin_inclusion,
    completePointMarkingOrigin_inclusion_assoc, completePointToIntegralCubic_marking,
    Category.assoc, originNeighborhoodSection_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
