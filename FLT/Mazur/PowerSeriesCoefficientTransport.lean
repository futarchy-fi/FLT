/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Detecting residue coefficients after injective transport

A transported power-series action through constant coefficients determines
both the original constant action and its factorization through the residue field.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PowerSeriesCoefficientTransport

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  (e : A →+* B) (ρ : PowerSeries K →+* A) (σ : K →+* B)
  (h : e.comp ρ = σ.comp PowerSeries.constantCoeff)

include h in
/-- Transport of constant series recovers the target coefficient homomorphism. -/
theorem constants : e.comp (ρ.comp PowerSeries.C) = σ := by
  ext a
  exact (DFunLike.congr_fun h (PowerSeries.C a)).trans (by simp)

include h in
/-- An injective transport detects the factorization through constant coefficients. -/
theorem factor (he : Function.Injective e) :
    ρ = (ρ.comp PowerSeries.C).comp PowerSeries.constantCoeff := by
  ext a
  apply he
  exact (DFunLike.congr_fun h a).trans
    (DFunLike.congr_fun (constants e ρ σ h) (PowerSeries.constantCoeff a)).symm

end FLT.Mazur.PowerSeriesCoefficientTransport
