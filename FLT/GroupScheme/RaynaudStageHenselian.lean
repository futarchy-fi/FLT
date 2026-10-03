/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFreeAdicComplete
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian

/-!
# Completeness and Henselianity of finite unramified stages

A finite domain stage over a complete DVR is free. When the maximal ideal
is extended from the base, finite free completeness makes the stage complete
at its own maximal ideal, hence Henselian.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace RaynaudParameters

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsDomain S] [IsLocalRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- A finite unramified domain stage over a complete DVR is complete. -/
theorem unramified_stage_complete
    (hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsAdicComplete (maximalIdeal S) S := by
  let : Module.Free R S := inferInstance
  rw [← hm]
  exact ThreeAdicPlan.adicComplete_finite_free_algebra (maximalIdeal R) S

/-- Hensel's lemma holds at every such finite stage. -/
theorem unramified_stage_henselian
    (hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    HenselianLocalRing S := by
  let := unramified_stage_complete hm
  constructor
  intro f hf x hx hd
  exact HenselianRing.is_henselian f hf x hx (hd.map (Ideal.Quotient.mk (maximalIdeal S)))

end RaynaudParameters
