/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupPointKernelTransport
public import FLT.Mazur.WeierstrassSmoothCompleteKernel
public import FLT.Mazur.OneGonCompleteCyclicLiftCriterion

/-!
# Bijective powers on the actual complete one-gon reduction kernel

Complete smooth-group root reconstruction discharges the kernel-power premise
for unit indices. The kernel is that of the original constant-coefficient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (n : ℕ)

/-- Unit-index powers are bijective on the full actual complete one-gon reduction kernel. -/
theorem completeSectionReduction_kernel_pow_bijective
    (hn : IsUnit (n : PowerSeries K)) :
    Function.Bijective (fun z : (completeSectionReduction K).ker ↦ z ^ n) := by
  let _ := (PowerSeries.constantCoeff (R := K)).toAlgebra
  let φ : PowerSeries K →ₐ[PowerSeries K] K :=
    ⟨PowerSeries.constantCoeff, fun _ ↦ rfl⟩
  let _ := PowerSeriesSmoothPointLift.constantCoeff_complete K
  have h := WeierstrassSmoothCompleteKernel.kernel_pow_bijective
    (equation (PowerSeries.X : PowerSeries K)) φ PowerSeries.constantCoeff_surj n hn
  let e : 𝟙_ (Over (Spec (.of (PowerSeries K)))) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) (PowerSeries K)))) :=
    Over.isoMk (Iso.refl _) (by simp)
  apply GroupPointKernelTransport.kernel_pow_bijective e (completeClosedTestMap K)
    (WeierstrassIntegralChart.smoothAlgebraTestMap φ) _ n h
  apply Over.OverMorphism.ext
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

variable (labels : Multiplicative (ZMod n) →*
  (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hn : IsUnit (n : PowerSeries K))

/-- The prescribed cyclic marking lifts over the original complete base at every unit index. -/
def unitIndexCompleteMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶
      (relativeGroup (PowerSeries.X : PowerSeries K)).X) :=
  correctedCompleteMarking K n labels (completeSectionReduction_kernel_pow_bijective K n hn)

/-- Complete cyclic lifting retains each full original closed label. -/
@[reassoc] theorem unitIndexCompleteMarking_reduction (a : Multiplicative (ZMod n)) :
    completeClosedTestMap K ≫ unitIndexCompleteMarking K n labels hn a =
      closedCyclicMarking K n labels a :=
  correctedCompleteMarking_reduction K n labels _ a

/-- The constructed complete marking preserves faithfulness of the original labels. -/
theorem unitIndexCompleteMarking_injective (h : Function.Injective labels) :
    Function.Injective (unitIndexCompleteMarking K n labels hn) :=
  correctedCompleteMarking_injective K n labels _ h

end FLT.Mazur.OneGonSmoothing
