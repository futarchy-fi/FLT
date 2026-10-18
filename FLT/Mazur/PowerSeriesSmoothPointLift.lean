/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCompleteResidueLift
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Smooth points lift over the actual power-series coefficient ring

The constant-coefficient kernel is the parameter ideal. Its completeness
therefore supplies an actual section retaining a prescribed closed point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PowerSeriesSmoothPointLift

/-- The actual closed coefficient kernel is exactly the parameter ideal. -/
theorem constantCoeff_kernel (R : Type*) [CommRing R] :
    RingHom.ker (PowerSeries.constantCoeff (R := R)) = Ideal.span {PowerSeries.X} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

/-- The original coefficient ring is complete for the kernel of closed reduction. -/
theorem constantCoeff_complete (R : Type*) [CommRing R] :
    IsAdicComplete (RingHom.ker (PowerSeries.constantCoeff (R := R))) (PowerSeries R) := by
  rw [constantCoeff_kernel]
  infer_instance

/-- Any prescribed closed point of a smooth scheme lifts over the same power-series base. -/
theorem exists_lift {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (.of (PowerSeries K))) [Smooth f] (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff)) :
    ∃ s : Spec (.of (PowerSeries K)) ⟶ X,
      Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ s = x ∧ s ≫ f = 𝟙 _ := by
  let _ := constantCoeff_complete K
  exact SmoothCompleteResidueLift.exists_lift f PowerSeries.constantCoeff
    PowerSeries.constantCoeff_surj x hx

end FLT.Mazur.PowerSeriesSmoothPointLift
