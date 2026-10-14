/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraph

/-!
# The graph modification is unchanged on the entire original smooth input

Schematic density and separatedness prove that the graph projection is an
isomorphism over the full smooth-input open, including contracted components.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "u" => completeIdentityActionSmoothToGraph K n h

/-- The full inverse image of the smooth-input open in the actual graph closure. -/
abbrev completeIdentityActionGraphSmoothOpen :
    (completeIdentityActionGraphClosure K n h).Opens := (p) ⁻¹ᵁ (V)
local notation "W" => completeIdentityActionGraphSmoothOpen K n h

/-- The existing smooth graph factors into the full inverse image, with no shrinking. -/
def completeIdentityActionGraphSmoothSection : (V).toScheme ⟶ (W).toScheme :=
  IsOpenImmersion.lift (W).ι (u) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change ((u) ≫ (p)) x ∈ (V)
    rw [completeIdentityActionSmoothToGraph_projection]
    exact x.2)

/-- Factoring the smooth graph leaves its original morphism unchanged. -/
@[reassoc] theorem completeIdentityActionGraphSmoothSection_inclusion :
    completeIdentityActionGraphSmoothSection K n h ≫ (W).ι = (u) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factored graph section is still schematically dense in the full inverse image. -/
instance completeIdentityActionGraphSmoothSection_schematic :
    IsSchemeTheoreticallyDominant (completeIdentityActionGraphSmoothSection K n h) := by
  let _ : NoetherianSpace (V).toScheme := NoetherianSpace.set ((V) : Set (P))
  let _ : QuasiCompact (completeIdentityActionGraphSmoothSection K n h ≫ (W).ι) :=
    quasiCompact_of_noetherianSpace_source _
  have : IsSchemeTheoreticallyDominant
      (completeIdentityActionGraphSmoothSection K n h ≫ (W).ι) := by
    rw [completeIdentityActionGraphSmoothSection_inclusion]
    infer_instance
  exact Chow.schematicallyDense_openFactor _ (W).ι

/-- The section is a right inverse to the restricted original graph projection. -/
@[reassoc] theorem completeIdentityActionGraphSmoothSection_projection :
    completeIdentityActionGraphSmoothSection K n h ≫ ((p) ∣_ (V)) = 𝟙 _ := by
  apply (cancel_mono (V).ι).mp
  rw [Category.assoc, morphismRestrict_ι,
    completeIdentityActionGraphSmoothSection_inclusion_assoc,
    completeIdentityActionSmoothToGraph_projection, Category.id_comp]

/-- Density excludes extra graph components or nilpotents over the full smooth-input open. -/
theorem completeIdentityActionGraphSmoothSection_retraction :
    ((p) ∣_ (V)) ≫ completeIdentityActionGraphSmoothSection K n h = 𝟙 _ := by
  refine Chow.schematicallyDense_ext ((W).ι ≫ (p)) ?_
    (completeIdentityActionGraphSmoothSection K n h) ?_
  · simp only [Category.assoc, completeIdentityActionGraphSmoothSection_inclusion_assoc,
      completeIdentityActionSmoothToGraph_projection, morphismRestrict_ι, Category.id_comp]
  · rw [← Category.assoc, completeIdentityActionGraphSmoothSection_projection,
      Category.id_comp, Category.comp_id]

/-- The actual graph closure is isomorphic to the original input on the entire smooth open. -/
def completeIdentityActionGraphSmoothIso : (W).toScheme ≅ (V).toScheme where
  hom := (p) ∣_ (V)
  inv := completeIdentityActionGraphSmoothSection K n h
  hom_inv_id := completeIdentityActionGraphSmoothSection_retraction K n h
  inv_hom_id := completeIdentityActionGraphSmoothSection_projection K n h

/-- The original graph projection has no modification at any smooth second input. -/
instance completeIdentityActionGraphProjection_smooth_isIso : IsIso ((p) ∣_ (V)) :=
  (completeIdentityActionGraphSmoothIso K n h).isIso_hom

end FLT.Mazur.PolygonInfinitesimalStages
