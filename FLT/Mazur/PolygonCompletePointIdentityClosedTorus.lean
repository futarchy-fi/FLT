/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityGroup

/-!
# The original identity open has the full retained torus as its closed fiber

The equality uses the actual original closed inclusion and the original
contraction square. In particular, no omitted component enters this open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeClosedFiberInclusion

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => integralCurveStructure (W)
local notation "U" => completePointIdentityOpen K n h i
local notation "j" => completeClosedFiberInclusion K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "t" => Over.Hom.left (torusToComponent K ≫ componentι K n i ≫ p)

/-- On the original closed polygon, the identity open is exactly its retained Laurent component. -/
theorem completePointIdentityOpen_closed_preimage :
    let _ := torus_isOpenImmersion K n (by omega) p q hp i
    (j) ⁻¹ᵁ (U) = (t).opensRange := by
  let _ := torus_isOpenImmersion K n (by omega) p q hp i
  have H := completePointToCubicBaseChange_isPullback K n h (completeClosedBase K)
    (j) (PolygonCyclicAtlas.toBase K n h) (completeClosedFiber_isPullback K n h) i
  change (j) ⁻¹ᵁ ((g) ⁻¹ᵁ (c).smoothLocus) = _
  rw [← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
  change (closedPointToCubic K n h i) ⁻¹ᵁ
    ((completePointCubicClosedInclusion K n h i) ⁻¹ᵁ (c).smoothLocus) = _
  rw [completePointCubicClosedInclusion_preimage_smooth, closedPointCubic_smoothLocus_eq_torus]
  apply TopologicalSpace.Opens.ext
  exact (CartesianFiniteFibers.range_eq_preimage
    (closedPointCubicTorus_isPullback K n h i)).symm

/-- The retained closed torus lifted to the actual full identity open. -/
def completePointIdentityClosedTorus : (MultiplicativeGroupScheme.gm K).left ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι ((t) ≫ (j)) (by
    let _ := torus_isOpenImmersion K n (by omega) p q hp i
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (t) x ∈ (j) ⁻¹ᵁ (U)
    rw [completePointIdentityOpen_closed_preimage]
    exact ⟨x, rfl⟩)

/-- The closed-torus inclusion retains the original Laurent normalization morphism. -/
@[reassoc] theorem completePointIdentityClosedTorus_inclusion :
    completePointIdentityClosedTorus K n h i ≫ (U).ι = (t) ≫ (j) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original closed polygon square cuts out exactly the full identity torus as a scheme. -/
theorem completePointIdentityClosedTorus_isPullback :
    IsPullback (completePointIdentityClosedTorus K n h i) (t) (U).ι (j) := by
  let _ := torus_isOpenImmersion K n (by omega) p q hp i
  apply IsOpenImmersion.isPullback
  · exact (completePointIdentityClosedTorus_inclusion K n h i).symm
  · rw [Scheme.Opens.opensRange_ι]
    exact completePointIdentityOpen_closed_preimage K n h i

end FLT.Mazur.PolygonInfinitesimalStages
