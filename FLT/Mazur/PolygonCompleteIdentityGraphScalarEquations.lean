/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartLocalEquations
public import FLT.Mazur.FlatSourceSectionKernel

/-!
# Cancelling complete-base scalars before specializing original graph equations

Every nonzero original power-series coefficient can be cancelled from a
smooth-graph equation before extending its full kernel to the first closed
fiber. No cancellation in the reduced coefficient ring is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "f" => completeIdentityActionSmoothGraph K n h
local notation "S" => Spec (CommRingCat.of (PowerSeries K))

/-- The original complete lifting space has its original source coefficient morphism. -/
def completeIdentityActionLiftSpaceStructure : completeIdentityActionLiftSpace K n h ⟶ S :=
  pullback.fst (completeIdentityActionTarget K n h 0)
    (completePointToIntegralCubic K n h 0) ≫ completeIdentityActionSecond K n h ≫
      exactVeroneseProjToBase K n h
local notation "s" => completeIdentityActionLiftSpaceStructure K n h

/-- The original smooth graph is flat over these actual complete-base coefficients. -/
instance completeIdentityActionSmoothGraph_structure_flat : Flat ((f) ≫ (s)) := by
  rw [completeIdentityActionLiftSpaceStructure,
    completeIdentityActionSmoothGraph_fst_assoc]
  infer_instance

attribute [local irreducible] completeIdentityActionLiftSpaceStructure
  completeIdentityActionSmoothGraph completeIdentityActionAdicChartSpaceMap
  completeIdentityActionAdicLiftSpaceMap
variable (V : (completeIdentityActionLiftSpace K n h).affineOpens)
local notation "b" => Scheme.Hom.appLE (s) ⊤ V (by simp)
local notation "q" => Iso.inv (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries K)))

/-- Every nonzero power-series scalar can be cancelled in the original local section kernel. -/
theorem completeIdentityActionSmoothGraph_cancel_scalar (a : PowerSeries K) (ha : a ≠ 0)
    (z : Γ(completeIdentityActionLiftSpace K n h, V))
    (hz : (f).app V ((b) ((q) a) * z) = 0) : (f).app V z = 0 := by
  have hr : IsRegular ((q) a) :=
    WeierstrassIntegralChart.flatRingHom_isRegular (q).hom
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (IsRegular.of_ne_zero ha)
  exact FlatSourceSectionKernel.cancel_base_scalar (f) (s) V ((q) a) hr z hz

/-- Arbitrary powers of the original smoothing parameter can be removed before specialization. -/
theorem completeIdentityActionSmoothGraph_cancel_parameter (r : ℕ)
    (z : Γ(completeIdentityActionLiftSpace K n h, V))
    (hz : (f).app V ((b) ((q) (PowerSeries.X ^ r)) * z) = 0) : (f).app V z = 0 :=
  completeIdentityActionSmoothGraph_cancel_scalar K n h V _
    (pow_ne_zero r PowerSeries.X_ne_zero) z hz

local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h 1 0 0 ≫
  completeIdentityActionAdicLiftSpaceMap K n h 1
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h

/-- The divided original equation lies in the actual full first closed-fiber ideal. -/
theorem completeIdentityFirstChartClosedLocalScalarEquation
    (U : (R).affineOpens) (e : U.1 ≤ (k) ⁻¹ᵁ V.1)
    (a : PowerSeries K) (ha : a ≠ 0)
    (z : Γ(completeIdentityActionLiftSpace K n h, V))
    (hz : (f).app V ((b) ((q) a) * z) = 0) :
    (k).appLE V U e z ∈
      (J).map ((R).presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom := by
  apply completeIdentityFirstChartClosedLocalEquation K n h U V e
  have hs := completeIdentityActionSmoothGraph_cancel_scalar K n h V a ha z hz
  change z ∈ RingHom.ker ((f).app V).hom at hs
  rw [completeIdentityActionSmoothGraph_affineKernel] at hs
  exact hs

end FLT.Mazur.PolygonInfinitesimalStages
