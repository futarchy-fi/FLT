/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourcePoleCubic

public import FLT.Mazur.PolygonCompletePointComplementCubicChart

/-!
# The actual target map into the full marking complement

Every parameter-zero receiving ring on the source-only localization has
an actual target map into the marking complement. Its cubic chart equals
the source cubic chart, preserving all receiving-ring nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "F" => completeIdentityFirstSourcePoleInputFunctions K n h U
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h 1 0 0
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityFirstSourcePolePatch K n h U →+* B)
variable (hf : φ (completeIdentityFirstSourcePoleParameter K n h U) = 0)

include hf

local notation "p" => (pullback.snd _ _ : (R) ⟶
  PolygonSmoothing.chart (Ring K 1) (parameter K 1))
local notation "a" => PolygonInfinitesimal.chart (Ring K 1) (parameter K 1) n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "r" => originalStageToCompatibleProj K n h 1

local notation "N" => completePointStageNodeOpen K n h 1 0 0
local notation "v" => Spec.map (CommRingCat.ofHom φ) ≫ (M) ≫
  Scheme.Opens.ι ((V).1) ≫ (p)
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1

/-- The original target lands in the entire marking complement. -/
theorem completeIdentityFirstSourcePole_target_range : Set.range (v) ⊆ Set.range (N).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  have hz := completeIdentityFirstSourcePole_mem_cubicZ K n h U φ hf z
  change (V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z)) ∈
    (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 at hz
  rw [completeIdentityAdicCubicZ_preimage K n h 1 0 0] at hz
  exact hz

/-- The full original target map, with only the source denominator inverted. -/
def completeIdentityFirstSourcePoleTargetComplement : Spec (.of B) ⟶ (N).toScheme :=
  IsOpenImmersion.lift (N).ι (v)
    (completeIdentityFirstSourcePole_target_range K n h U φ hf)
local notation "q" => completeIdentityFirstSourcePoleTargetComplement K n h U φ hf

/-- The complement factorization retains the original target scheme map. -/
@[reassoc] theorem completeIdentityFirstSourcePoleTargetComplement_inclusion :
    (q) ≫ (N).ι = (v) := IsOpenImmersion.lift_fac _ _ _

/-- Chart monomorphy compares the actual target complement with the source cubic chart. -/
theorem completeIdentityFirstSourcePole_complementCubic :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (S)) ≫ (d) =
      (q) ≫ completePointStageComplementToCubicChart K n h 1 0 0 := by
  apply (cancel_mono (integralCurveChart (E) 2)).mp
  simp only [Category.assoc]
  rw [completeIdentityFirstSourcePole_targetCubic K n h U φ hf,
    completePointStageComplementToCubicChart_inclusion K n h 1 0 0,
    completeIdentityFirstSourcePoleTargetComplement_inclusion_assoc K n h U φ hf]

local notation "ψ" => completePointNodeComplementFunctions K n h 1 0 0 (q)

/-- Every original cubic function has the same source and target pullback. -/
theorem completeIdentityFirstSourcePole_complementFunctions (z : Coordinate (E) 2) :
    φ ((S) (completePointNodeCubicFunctions K n h 1 0 0 z)) =
      (ψ) (completePointStageComplementCubicFunctions K n h 1 0 0 z) := by
  have he := congrArg (fun w ↦ (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv ≫
    w.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom)
    (completeIdentityFirstSourcePole_complementCubic K n h U φ hf)
  simp only [Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.ΓSpecIso_naturality_assoc] at he
  exact congrArg (fun w : CommRingCat.of (Coordinate (E) 2) ⟶ CommRingCat.of B ↦ w z) he

/-- The two retained pole functions agree without any target denominator localization. -/
theorem completeIdentityFirstSourcePole_complementPoles :
    φ ((S) (completePointNodeLocalizedPoleTwo K n h 1 0 0)) =
        (ψ) (completePointStageNodePoleTwo K n h 1 0 0) ∧
      φ ((S) (completePointNodeLocalizedPoleThree K n h 1 0 0)) =
        (ψ) (completePointStageNodePoleThree K n h 1 0 0) := by
  constructor
  · simpa only [completePointNodeCubicFunctions_coordinate,
      completePointStageComplementCubicFunctions_coordinate, completePointStageNodeCubic_X,
      Matrix.cons_val_zero] using
      completeIdentityFirstSourcePole_complementFunctions K n h U φ hf (coord (E) 2 0)
  · simpa only [completePointNodeCubicFunctions_coordinate,
      completePointStageComplementCubicFunctions_coordinate, completePointStageNodeCubic_Y,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      completeIdentityFirstSourcePole_complementFunctions K n h U φ hf (coord (E) 2 1)

end FLT.Mazur.PolygonInfinitesimalStages
