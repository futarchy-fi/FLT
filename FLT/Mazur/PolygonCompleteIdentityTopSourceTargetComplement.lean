/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopSourcePoleCubic

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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "Z" => CompleteIdentityTopSourcePolePatch K n h m U
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityTopAmbientParameter K n h m))
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "F" => completeIdentityTopSourcePoleInputFunctions K n h m U
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "d" => completePointNodeToCubicChart K n h (m + 1) 0 0
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityTopSourcePolePatch K n h m U →+* B)
variable (hf : φ (completeIdentityTopSourcePoleParameter K n h m U) = 0)

include hf

local notation "p" => (pullback.snd _ _ : (R) ⟶
  PolygonSmoothing.chart (Ring K (m + 1)) (parameter K (m + 1)))
local notation "a" => PolygonInfinitesimal.chart
  (Ring K (m + 1)) (parameter K (m + 1)) n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "r" => originalStageToCompatibleProj K n h (m + 1)

local notation "N" => completePointStageNodeOpen K n h (m + 1) 0 0
local notation "v" => Spec.map (CommRingCat.ofHom φ) ≫ (M) ≫
  Scheme.Opens.ι ((V).1) ≫ (p)
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h (m + 1) 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h (m + 1)

/-- The original target lands in the entire marking complement. -/
theorem completeIdentityTopSourcePole_target_range : Set.range (v) ⊆ Set.range (N).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  have hz := completeIdentityTopSourcePole_mem_cubicZ K n h m U φ hf z
  change (V).1.ι ((M) ((Spec.map (CommRingCat.ofHom φ)) z)) ∈
    (κ) ⁻¹ᵁ completeIdentityCubicChartOpen K n h 2 at hz
  rw [completeIdentityAdicCubicZ_preimage K n h (m + 1) 0 0] at hz
  exact hz

/-- The full original target map, with only the source denominator inverted. -/
def completeIdentityTopSourcePoleTargetComplement : Spec (.of B) ⟶ (N).toScheme :=
  IsOpenImmersion.lift (N).ι (v)
    (completeIdentityTopSourcePole_target_range K n h m U φ hf)
local notation "q" => completeIdentityTopSourcePoleTargetComplement K n h m U φ hf

/-- The complement factorization retains the original target scheme map. -/
@[reassoc] theorem completeIdentityTopSourcePoleTargetComplement_inclusion :
    (q) ≫ (N).ι = (v) := IsOpenImmersion.lift_fac _ _ _

/-- Chart monomorphy compares the actual target complement with the source cubic chart. -/
theorem completeIdentityTopSourcePole_complementCubic :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (S)) ≫ (d) =
      (q) ≫ completePointStageComplementToCubicChart K n h (m + 1) 0 0 := by
  apply (cancel_mono (integralCurveChart (E) 2)).mp
  simp only [Category.assoc]
  rw [completeIdentityTopSourcePole_targetCubic K n h m U φ hf,
    completePointStageComplementToCubicChart_inclusion K n h (m + 1) 0 0,
    completeIdentityTopSourcePoleTargetComplement_inclusion_assoc K n h m U φ hf]

local notation "ψ" => completePointNodeComplementFunctions K n h (m + 1) 0 0 (q)

/-- Every original cubic function has the same source and target pullback. -/
theorem completeIdentityTopSourcePole_complementFunctions (z : Coordinate (E) 2) :
    φ ((S) (completePointNodeCubicFunctions K n h (m + 1) 0 0 z)) =
      (ψ) (completePointStageComplementCubicFunctions K n h (m + 1) 0 0 z) := by
  have he := congrArg (fun w ↦ (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv ≫
    w.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom)
    (completeIdentityTopSourcePole_complementCubic K n h m U φ hf)
  simp only [Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.ΓSpecIso_naturality_assoc] at he
  exact congrArg (fun w : CommRingCat.of (Coordinate (E) 2) ⟶ CommRingCat.of B ↦ w z) he

/-- The two retained pole functions agree without any target denominator localization. -/
theorem completeIdentityTopSourcePole_complementPoles :
    φ ((S) (completePointNodeLocalizedPoleTwo K n h (m + 1) 0 0)) =
        (ψ) (completePointStageNodePoleTwo K n h (m + 1) 0 0) ∧
      φ ((S) (completePointNodeLocalizedPoleThree K n h (m + 1) 0 0)) =
        (ψ) (completePointStageNodePoleThree K n h (m + 1) 0 0) := by
  constructor
  · simpa only [completePointNodeCubicFunctions_coordinate,
      completePointStageComplementCubicFunctions_coordinate, completePointStageNodeCubic_X,
      Matrix.cons_val_zero] using
      completeIdentityTopSourcePole_complementFunctions K n h m U φ hf (coord (E) 2 0)
  · simpa only [completePointNodeCubicFunctions_coordinate,
      completePointStageComplementCubicFunctions_coordinate, completePointStageNodeCubic_Y,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      completeIdentityTopSourcePole_complementFunctions K n h m U φ hf (coord (E) 2 1)

end FLT.Mazur.PolygonInfinitesimalStages
