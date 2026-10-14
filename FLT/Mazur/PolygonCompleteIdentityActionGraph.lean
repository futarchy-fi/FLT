/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionSource
public import FLT.Mazur.PolygonCompletePointSurjective
public import FLT.Mazur.ChowSourceClosure

/-!
# The actual schematic graph closure of the original smooth lift

Close the constructed smooth lift inside the pullback of the original
contraction along the whole cubic action target. This produces a proper
polygon-valued correspondence, not yet a lift on the original input product.
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
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)

/-- The entire lifting space uses the unchanged original contraction and cubic action. -/
abbrev completeIdentityActionLiftSpace : Scheme := pullback (a) (g)

/-- The existing smooth lift gives an actual graph inside the original lifting space. -/
def completeIdentityActionSmoothGraph :
    (V).toScheme ⟶ completeIdentityActionLiftSpace K n h :=
  pullback.lift (V).ι (completeIdentityActionSmoothLift K n h)
    (completeIdentityActionSmoothLift_contraction K n h).symm

/-- The graph retains every original smooth input. -/
@[reassoc] theorem completeIdentityActionSmoothGraph_fst :
    completeIdentityActionSmoothGraph K n h ≫ pullback.fst (a) (g) = (V).ι :=
  pullback.lift_fst _ _ _

/-- The graph retains the constructed polygon-valued smooth lift. -/
@[reassoc] theorem completeIdentityActionSmoothGraph_snd :
    completeIdentityActionSmoothGraph K n h ≫ pullback.snd (a) (g) =
      completeIdentityActionSmoothLift K n h := pullback.lift_snd _ _ _

/-- The graph is an immersion because its first coordinate is the original open inclusion. -/
instance completeIdentityActionSmoothGraph_immersion :
    IsImmersion (completeIdentityActionSmoothGraph K n h) := by
  have : IsImmersion (completeIdentityActionSmoothGraph K n h ≫ pullback.fst (a) (g)) := by
    rw [completeIdentityActionSmoothGraph_fst]
    infer_instance
  exact IsImmersion.of_comp _ (pullback.fst (a) (g))

/-- Noetherianity makes taking the actual scheme-theoretic graph image legitimate. -/
instance completeIdentityActionSmoothGraph_quasiCompact :
    QuasiCompact (completeIdentityActionSmoothGraph K n h) := by
  let _ : NoetherianSpace (V).toScheme := NoetherianSpace.set ((V) : Set (P))
  exact quasiCompact_of_noetherianSpace_source _

/-- The closure retains the full kernel ideal of the graph, with no radical replacement. -/
def completeIdentityActionGraphClosure : Scheme :=
  (completeIdentityActionSmoothGraph K n h).image

/-- The actual closed graph inclusion into the original contraction pullback. -/
def completeIdentityActionGraphInclusion :
    completeIdentityActionGraphClosure K n h ⟶ completeIdentityActionLiftSpace K n h :=
  (completeIdentityActionSmoothGraph K n h).imageι

instance completeIdentityActionGraphInclusion_closed :
    IsClosedImmersion (completeIdentityActionGraphInclusion K n h) := by
  unfold completeIdentityActionGraphInclusion
  infer_instance

/-- The graph closure projects to the original entire action input product. -/
def completeIdentityActionGraphProjection : completeIdentityActionGraphClosure K n h ⟶ (P) :=
  completeIdentityActionGraphInclusion K n h ≫ pullback.fst (a) (g)

/-- The graph closure carries a constructed map to the unchanged original polygon. -/
def completeIdentityActionGraphLift :
    completeIdentityActionGraphClosure K n h ⟶ exactVeroneseProj K n h :=
  completeIdentityActionGraphInclusion K n h ≫ pullback.snd (a) (g)

/-- The original smooth input is an actual open of the schematic graph closure. -/
def completeIdentityActionSmoothToGraph :
    (V).toScheme ⟶ completeIdentityActionGraphClosure K n h :=
  (completeIdentityActionSmoothGraph K n h).toImage

instance completeIdentityActionSmoothToGraph_open :
    IsOpenImmersion (completeIdentityActionSmoothToGraph K n h) := by
  unfold completeIdentityActionSmoothToGraph
  infer_instance

instance completeIdentityActionSmoothToGraph_schematic :
    IsSchemeTheoreticallyDominant (completeIdentityActionSmoothToGraph K n h) :=
  Chow.toImage_schemeTheoreticallyDominant _

/-- The dense smooth graph recovers the actual ambient graph map. -/
@[reassoc] theorem completeIdentityActionSmoothToGraph_inclusion :
    completeIdentityActionSmoothToGraph K n h ≫ completeIdentityActionGraphInclusion K n h =
      completeIdentityActionSmoothGraph K n h := Scheme.Hom.toImage_imageι _

/-- The graph projection restricts to the original smooth-input inclusion. -/
@[reassoc] theorem completeIdentityActionSmoothToGraph_projection :
    completeIdentityActionSmoothToGraph K n h ≫ completeIdentityActionGraphProjection K n h =
      (V).ι := by
  rw [completeIdentityActionGraphProjection,
    completeIdentityActionSmoothToGraph_inclusion_assoc, completeIdentityActionSmoothGraph_fst]

/-- The graph's polygon map restricts to the original smooth lift. -/
@[reassoc] theorem completeIdentityActionSmoothToGraph_lift :
    completeIdentityActionSmoothToGraph K n h ≫ completeIdentityActionGraphLift K n h =
      completeIdentityActionSmoothLift K n h := by
  rw [completeIdentityActionGraphLift,
    completeIdentityActionSmoothToGraph_inclusion_assoc, completeIdentityActionSmoothGraph_snd]

/-- The whole graph, including every exceptional input, retains the exact contraction square. -/
@[reassoc] theorem completeIdentityActionGraphLift_contraction :
    completeIdentityActionGraphLift K n h ≫ (g) =
      completeIdentityActionGraphProjection K n h ≫ (a) := by
  simp only [completeIdentityActionGraphLift, completeIdentityActionGraphProjection,
    Category.assoc, pullback.condition]

/-- The actual graph modification is proper over the original action input. -/
instance completeIdentityActionGraphProjection_proper :
    IsProper (completeIdentityActionGraphProjection K n h) := by
  let _ := completePointToIntegralCubic_proper K n h (0 : Fin n)
  unfold completeIdentityActionGraphProjection
  infer_instance

/-- Properness and the dense original smooth domain give all original inputs preimages. -/
instance completeIdentityActionGraphProjection_surjective :
    Surjective (completeIdentityActionGraphProjection K n h) := by
  constructor
  rw [← Set.range_eq_univ]
  apply Set.eq_univ_of_univ_subset
  rw [← (completeIdentityActionSmooth_dense K n h).closure_eq]
  apply closure_minimal _ (completeIdentityActionGraphProjection K n h).isClosedMap.isClosed_range
  intro x hx
  refine ⟨completeIdentityActionSmoothToGraph K n h ⟨x, hx⟩, ?_⟩
  change (completeIdentityActionSmoothToGraph K n h ≫
    completeIdentityActionGraphProjection K n h) ⟨x, hx⟩ = x
  rw [completeIdentityActionSmoothToGraph_projection]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
