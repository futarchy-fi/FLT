/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityOpenSquare

/-!
# The entire original identity on the flattened cubic neighborhood

The neighborhood contains the complete zero section, not just its closed
point. Its inverse image contains the original marking on the complete family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointIdentityAffineOpen completePointToOrigin completePointOriginOpen
  completePointWeierstrassCurve completePointIdentityIsoOpen completePointIdentityCubicOpen
  completePointIdentityAffineTargetMarking

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "s" => completeBaseMarking K n h i
local notation "U" => completePointIdentityAffineOpen K n h i
local notation "B" => completePointIdentityIsoOpen K n h i
local notation "T" => completePointIdentityCubicOpen K n h i
local notation "mT" => completePointIdentityAffineTargetMarking K n h i

/-- Lift the original full affine marking to the chosen principal neighborhood. -/
def completePointIdentityPrincipalMarking : S₀ ⟶ (B).toScheme :=
  IsOpenImmersion.lift (B).ι (mT) (by
    rw [Scheme.Opens.range_ι]
    exact (completePointIdentityIsoOpen_spec K n h i).1)

/-- The principal lift retains the unchanged marking morphism. -/
@[reassoc] theorem completePointIdentityPrincipalMarking_inclusion :
    completePointIdentityPrincipalMarking K n h i ≫ (B).ι = (mT) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The principal chart marking is precisely the zero section of the original cubic. -/
@[reassoc] theorem completePointIdentityPrincipalMarking_toCubic :
    completePointIdentityPrincipalMarking K n h i ≫
      completePointIdentityTargetInclusion K n h i =
        (S₀).toSpecΓ ≫ integralCurveZero (W) := by
  rw [completePointIdentityTargetInclusion,
    completePointIdentityPrincipalMarking_inclusion_assoc,
    completePointIdentityAffineTargetMarking_inclusion_assoc,
    originNeighborhoodSection_inclusion]

/-- The actual flattened target open contains every point of the cubic zero section. -/
theorem completePointIdentityCubicOpen_zero_range :
    Set.range (integralCurveZero (W)) ⊆ (T) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := (inferInstance : Surjective (S₀).toSpecΓ).1 x
  rw [completePointIdentityCubicOpen]
  change integralCurveZero (W) ((S₀).toSpecΓ y) ∈
    Set.range (completePointIdentityTargetInclusion K n h i)
  exact ⟨completePointIdentityPrincipalMarking K n h i y,
    congrArg (fun k => k y) (completePointIdentityPrincipalMarking_toCubic K n h i)⟩

/-- The actual source neighborhood contains the entire original marking. -/
theorem completePointIdentityCubicOpen_marking_range : Set.range (s) ⊆ (g) ⁻¹ᵁ (T) := by
  rintro _ ⟨x, rfl⟩
  have he := congrArg (fun k => k x) (completePointToIntegralCubic_marking K n h i)
  change (g) ((s) x) ∈ (T)
  rw [← Scheme.Hom.comp_apply, he]
  exact completePointIdentityCubicOpen_zero_range K n h i ⟨_, rfl⟩

/-- The flattened source neighborhood and the original marking complement cover the family. -/
theorem completePointIdentityCubicOpen_complement_cover :
    (g) ⁻¹ᵁ (T) ⊔ (s).ker.support.compl = ⊤ := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := isClosedImmersion_section _ _ (completeBaseMarking_toBase K n h i)
  apply top_unique
  intro x _
  by_cases hx : x ∈ Set.range (s)
  · exact Or.inl (completePointIdentityCubicOpen_marking_range K n h i hx)
  · right
    change x ∉ ((s).ker.support : Set _)
    simpa only [Scheme.Hom.support_ker,
      (s).isClosedMap.isClosed_range.closure_eq] using hx

end FLT.Mazur.PolygonInfinitesimalStages
