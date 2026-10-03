/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexTiltGalois
public import Mathlib.Topology.Algebra.Ring.Ideal

/-! # Joint continuity on the integral tilt with its inverse-limit topology

The mod-p ring has the quotient topology from O_C. The integral tilt is
topologized by its inverse-Frobenius coordinates. No identification with
the topology of its valuation is asserted here.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The induced quotient action is jointly continuous. -/
theorem complexModPGalois_continuous :
    Continuous (fun z : PadicGalois p × ModP 𝓞_ℂ_[p] p ↦ complexModPGalois p z.1 z.2) := by
  have hq := ((IsOpenQuotientMap.id (X := PadicGalois p)).prodMap
    (QuotientRing.isOpenQuotientMap_mk (Ideal.span {(p : 𝓞_ℂ_[p])}))).isQuotientMap
  apply hq.continuous_iff.mpr
  exact continuous_quot_mk.comp
    (continuous_smul : Continuous (fun z : PadicGalois p × 𝓞_ℂ_[p] ↦ z.1 • z.2))

/-- The inverse-limit topology on the actual integral tilt. -/
instance instTopologicalSpaceIntegralTilt : TopologicalSpace (IntegralTilt p) :=
  TopologicalSpace.induced (fun x : IntegralTilt p ↦ fun n : ℕ ↦ PreTilt.coeff n x) inferInstance

/-- The coordinate map into the product is continuous by construction. -/
theorem integralTilt_coordinates_continuous :
    Continuous (fun x : IntegralTilt p ↦ fun n : ℕ ↦ PreTilt.coeff n x) :=
  continuous_induced_dom

/-- Each inverse-Frobenius coordinate is continuous. -/
theorem integralTilt_coeff_continuous (n : ℕ) :
    Continuous (PreTilt.coeff n : IntegralTilt p → ModP 𝓞_ℂ_[p] p) :=
  (continuous_apply n).comp (integralTilt_coordinates_continuous p)

/-- Coordinatewise quotient continuity proves joint continuity on the tilt. -/
instance instContinuousSMulIntegralTilt : ContinuousSMul (PadicGalois p) (IntegralTilt p) where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro n
    change Continuous (fun z : PadicGalois p × IntegralTilt p ↦
      complexModPGalois p z.1 (PreTilt.coeff n z.2))
    have h := (complexModPGalois_continuous p).comp
      ((continuous_fst : Continuous (fun z : PadicGalois p × IntegralTilt p ↦ z.1)).prodMk
        ((integralTilt_coeff_continuous p n).comp continuous_snd))
    exact h

end PadicHodgeTheory
