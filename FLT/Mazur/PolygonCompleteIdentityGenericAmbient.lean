/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericContractionExt
public import FLT.Mazur.PolygonCompleteIdentityGraphScalarEquations

/-!
# The entire generic ambient relation factors through the original smooth graph

Both original polygon coordinates lie over the same generic coefficient
field. The source is therefore smooth, and the contraction detects the
unchanged target coordinate. This constructs a smooth-graph factorization
of every generic ambient point as a morphism, including its scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "Y" => completeIdentityActionLiftSpace K n h
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "π" => exactVeroneseProjToBase K n h
local notation "c" => completePointToIntegralCubic K n h 0
local notation "a" => completeIdentityActionTarget K n h 0
local notation "s" => completeIdentityActionLiftSpaceStructure K n h
local notation "v" => completeIdentityActionSecond K n h
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "L" => FractionRing (PowerSeries K)
local notation "α" => algebraMap (PowerSeries K) (L)
local notation "b" => Spec.map (CommRingCat.ofHom (α))

/-- The original ambient target retains exactly the original source's base parameter. -/
@[reassoc] theorem completeIdentityActionLiftSpace_target_structure :
    pullback.snd (a) (c) ≫ (π) = (s) := by
  apply (cancel_mono (S).toSpecΓ).mp
  rw [Category.assoc, ← completePointToIntegralCubic_over,
    ← pullback.condition_assoc, completeIdentityActionTarget_structure]
  rfl

/-- The whole generic fiber of the original complete lifting space. -/
abbrev completeIdentityActionGenericAmbient : Scheme := pullback (s) (b)

/-- The original generic ambient inclusion, before taking any graph image. -/
abbrev completeIdentityActionGenericAmbientInclusion := pullback.fst (s) (b)
local notation "r" => completeIdentityActionGenericAmbientInclusion K n h
local notation "q" => pullback.snd (s) (b)

/-- The original parameter remains nonzero in the actual generic coefficient field. -/
theorem completeIdentityGenericParameter_ne_zero : (α) PowerSeries.X ≠ 0 := by
  intro hz
  exact PowerSeries.X_ne_zero ((IsFractionRing.injective (PowerSeries K) (L))
    (hz.trans (map_zero (α)).symm))

/-- The source coordinate of the entire generic ambient space is an original smooth input. -/
def completeIdentityActionGenericAmbientToSmooth :
    completeIdentityActionGenericAmbient K n h ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι ((r) ≫ pullback.fst (a) (c)) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hr := completeGenericMap_preimage_identity K n h 0 (L) (α)
      (completeIdentityGenericParameter_ne_zero K) ((r) ≫ pullback.fst (a) (c) ≫ (v)) (q)
      (by simpa only [completeIdentityActionLiftSpaceStructure, Category.assoc] using
        (show (r) ≫ (s) = (q) ≫ (b) from pullback.condition))
    exact completePointIdentityOpen_le_smooth K n h 0
      (hr.ge (show x ∈ ⊤ from trivial)))
local notation "l" => completeIdentityActionGenericAmbientToSmooth K n h

/-- The constructed smooth input is exactly the original generic source coordinate. -/
@[reassoc] theorem completeIdentityActionGenericAmbientToSmooth_inclusion :
    (l) ≫ (V).ι = (r) ≫ pullback.fst (a) (c) := IsOpenImmersion.lift_fac _ _ _

/-- Generic contraction uniqueness recovers the actual target coordinate as well. -/
@[reassoc] theorem completeIdentityActionGenericAmbientToSmooth_target :
    (l) ≫ completeIdentityActionSmoothLift K n h = (r) ≫ pullback.snd (a) (c) := by
  apply completeGeneric_contraction_ext K n h 0 (L) (α)
    (completeIdentityGenericParameter_ne_zero K) _ _ (q)
  · rw [Category.assoc, completeIdentityActionSmoothLift_structure,
      completeIdentityActionGenericAmbientToSmooth_inclusion_assoc]
    exact pullback.condition
  · rw [Category.assoc, completeIdentityActionLiftSpace_target_structure]
    exact pullback.condition
  · rw [Category.assoc, completeIdentityActionSmoothLift_contraction,
      completeIdentityActionGenericAmbientToSmooth_inclusion_assoc,
      Category.assoc, pullback.condition]

/-- The whole generic ambient relation factors through the original complete smooth graph. -/
@[reassoc] theorem completeIdentityActionGenericAmbientToSmooth_graph : (l) ≫ (f) = (r) := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityActionSmoothGraph_fst,
      completeIdentityActionGenericAmbientToSmooth_inclusion]
  · rw [Category.assoc, completeIdentityActionSmoothGraph_snd,
      completeIdentityActionGenericAmbientToSmooth_target]

end FLT.Mazur.PolygonInfinitesimalStages
