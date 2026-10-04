/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorSectionExact
public import Mathlib.RingTheory.Length

/-!
# Cartier-chart cokernels

The cokernel of the actual canonical section map on a Cartier chart is
linearly isomorphic to the quotient by the actual divisor ideal. In particular
its module length equals the quotient length. The coordinate isomorphism uses
the chosen Cartier equation; no global trivialization of O(D) is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {I : X.IdealSheafData} {U : X.affineOpens}

/-- The actual canonical map on affine sections, retaining its module structure. -/
def divisorSectionLinear (hI : EffectiveCartier I) (U : X.affineOpens) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(divisorLineBundle I hI, U.1) :=
  ((divisorSectionMap hI).val.app (op U.1)).hom

/-- Cartier coordinates followed by the actual ideal quotient. -/
def CartierChart.divisorQuotientMap (hU : CartierChart I U) (hI : EffectiveCartier I) :
    Γ(divisorLineBundle I hI, U.1) →ₗ[Γ(X, U)] Γ(X, U) ⧸ I.ideal U :=
  (I.ideal U).mkQ.comp ((hU.divisorSectionsEquiv hI).trans hU.dualEquiv).toLinearMap

/-- The chart quotient map is surjective. -/
theorem CartierChart.divisorQuotientMap_surjective (hU : CartierChart I U)
    (hI : EffectiveCartier I) : Function.Surjective (hU.divisorQuotientMap hI) :=
  (Submodule.mkQ_surjective _).comp
    ((hU.divisorSectionsEquiv hI).trans hU.dualEquiv).surjective

/-- The chart quotient kernel is precisely the image of the actual canonical section. -/
theorem CartierChart.divisorQuotientMap_exact (hU : CartierChart I U)
    (hI : EffectiveCartier I) :
    Function.Exact (divisorSectionLinear hI U) (hU.divisorQuotientMap hI) := by
  intro s
  have hm (r : Γ(X, U)) : r ∈ I.ideal U ↔ hU.choose ∣ r := by
    conv_lhs => rw [hU.choose_spec.2]
    exact Ideal.mem_span_singleton
  change Submodule.Quotient.mk (hU.dualEquiv (divisorChartEval I U s)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, hm]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ((hU.divisorSectionsEquiv hI).trans hU.dualEquiv).injective ?_⟩
    change hU.dualEquiv (divisorChartEval I U ((divisorSectionMap hI).app U.1 r)) = _
    rw [divisorSectionMap_coordinate]
    exact (mul_comm r hU.choose).trans hr.symm
  · rintro ⟨r, rfl⟩
    refine ⟨r, ?_⟩
    change hU.dualEquiv (divisorChartEval I U ((divisorSectionMap hI).app U.1 r)) = _
    rw [divisorSectionMap_coordinate, mul_comm]

/-- The actual section-module cokernel is the quotient by the actual Cartier ideal. -/
def CartierChart.divisorCokernelEquiv (hU : CartierChart I U) (hI : EffectiveCartier I) :
    (Γ(divisorLineBundle I hI, U.1) ⧸ LinearMap.range (divisorSectionLinear hI U)) ≃ₗ[Γ(X, U)]
      Γ(X, U) ⧸ I.ideal U :=
  (Submodule.quotEquivOfEq _ _ (hU.divisorQuotientMap_exact hI).linearMap_ker_eq.symm).trans
    ((hU.divisorQuotientMap hI).quotKerEquivOfSurjective (hU.divisorQuotientMap_surjective hI))

/-- Cartier-chart cokernel length is the divisor quotient length. -/
theorem CartierChart.divisorCokernel_length (hU : CartierChart I U) (hI : EffectiveCartier I) :
    Module.length Γ(X, U)
        (Γ(divisorLineBundle I hI, U.1) ⧸ LinearMap.range (divisorSectionLinear hI U)) =
      Module.length Γ(X, U) (Γ(X, U) ⧸ I.ideal U) :=
  (hU.divisorCokernelEquiv hI).length_eq

end FLT.Mazur.FCurve
