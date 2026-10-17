/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenSpectrumFunctions
public import FLT.Mazur.PolygonCompleteIdentityTopPolePatchMaps

/-!
# The original common pole patch as a scheme

The spectrum of the common denominator localization maps to the original
adic affine patch. Its target projection is exactly the retained target
homomorphism, including every original nilpotent.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "Z" => CompleteIdentityTopPolePatch K n h m U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "Q" => completeIdentityTopPoleTargetMap K n h m U
local notation "η" => algebraMap (ChartRing (parameter K (m + 1))) (StageNodeLocalization K (m + 1))
local notation "p" => (pullback.snd _ _ : (R) ⟶ chart (Ring K (m + 1)) (parameter K (m + 1)))

/-- The common pole localization maps into the unchanged original adic patch. -/
def completeIdentityTopPolePatchMap : Spec (.of (Z)) ⟶ (V).1.toScheme :=
  AffineOpenSpectrumFunctions.map (V) (CommRingCat.ofHom (ι))

/-- Its section map is the original localization homomorphism. -/
theorem completeIdentityTopPolePatchMap_appTop :
    (completeIdentityTopPolePatchMap K n h m U).appTop =
      (V).1.topIso.hom ≫ CommRingCat.ofHom (ι) ≫ (Scheme.ΓSpecIso (.of (Z))).inv :=
  AffineOpenSpectrumFunctions.map_appTop _ _

/-- The target projection factors through the same original localized node. -/
@[reassoc] theorem completeIdentityTopPolePatchMap_target :
    completeIdentityTopPolePatchMap K n h m U ≫ (V).1.ι ≫ (p) =
      Spec.map (CommRingCat.ofHom (Q)) ≫ Spec.map (CommRingCat.ofHom (η)) := by
  rw [completeIdentityTopPolePatchMap,
    AffineOpenSpectrumFunctions.map_comp_inclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (completeIdentityTopPoleTargetMap_algebraMap K n h m U z).symm

end FLT.Mazur.PolygonInfinitesimalStages
