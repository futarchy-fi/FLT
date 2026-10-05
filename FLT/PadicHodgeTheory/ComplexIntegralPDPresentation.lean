/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.IntegralPDPresentation
public import FLT.PadicHodgeTheory.ComplexDividedPowerHull

/-!
# The integral theta presentation and its map to the embedded hull

Apply the integral construction to the actual theta kernel. Its map to the
embedded hull preserves the original A_inf coefficients and divided powers.
Injectivity, a PD structure on the presentation, and p-compatibility are not asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The integral presentation uses the actual kernel before inverting p. -/
abbrev ComplexIntegralPDPresentation := IntegralPDPresentation (RingHom.ker (complexTheta p))

/-- Every original theta-kernel element lies in the embedded hull's PD ideal. -/
theorem complexThetaKernel_toPDHull (x : RingHom.ker (complexTheta p)) :
    complexAinfToPDHull p x ∈ complexPDHullIdeal p := by
  change complexThetaInvertP p (algebraMap (Ainf p) (ComplexAinfInvertP p) x) = 0
  rw [complexThetaInvertP_algebraMap, x.property, map_zero]

/-- The integral presentation maps to the embedded theta hull without cancelling factorials. -/
def complexIntegralPDToHull : ComplexIntegralPDPresentation p →+* ComplexAinfPDHull p := by
  let : Algebra (Ainf p) (ComplexAinfPDHull p) := (complexAinfToPDHull p).toAlgebra
  exact (integralPDTargetMap (RingHom.ker (complexTheta p)) (complexPDHullIdeal p)
    (complexPDHullDividedPowers p) (complexThetaKernel_toPDHull p)).toRingHom

/-- The map retains the original coefficient map from A_inf. -/
theorem complexIntegralPDToHull_base (x : Ainf p) :
    complexIntegralPDToHull p (algebraMap (Ainf p) (ComplexIntegralPDPresentation p) x) =
      complexAinfToPDHull p x := by
  let : Algebra (Ainf p) (ComplexAinfPDHull p) := (complexAinfToPDHull p).toAlgebra
  exact (integralPDTargetMap (RingHom.ker (complexTheta p)) (complexPDHullIdeal p)
    (complexPDHullDividedPowers p) (complexThetaKernel_toPDHull p)).commutes x

/-- Every symbol maps to the corresponding actual divided power in the hull. -/
theorem complexIntegralPDToHull_symbol (n : ℕ) (x : RingHom.ker (complexTheta p)) :
    complexIntegralPDToHull p (integralPDSymbol _ n x) =
      (complexPDHullDividedPowers p).dpow n (complexAinfToPDHull p x) := by
  let : Algebra (Ainf p) (ComplexAinfPDHull p) := (complexAinfToPDHull p).toAlgebra
  exact integralPDTargetMap_symbol (RingHom.ker (complexTheta p)) (complexPDHullIdeal p)
    (complexPDHullDividedPowers p) (complexThetaKernel_toPDHull p) n x

/-- The integral presentation maps to the already constructed de Rham completion. -/
def complexIntegralPDToDeRham : ComplexIntegralPDPresentation p →+* ComplexBDeRhamPlus p :=
  (complexPDHullToDeRham p).comp (complexIntegralPDToHull p)

/-- This de Rham comparison still extends the original A_inf map. -/
theorem complexIntegralPDToDeRham_base (x : Ainf p) :
    complexIntegralPDToDeRham p (algebraMap (Ainf p) (ComplexIntegralPDPresentation p) x) =
      complexAinfToDeRham p x := by
  rw [complexIntegralPDToDeRham, RingHom.comp_apply, complexIntegralPDToHull_base,
    complexPDHullToDeRham_integral]

end PadicHodgeTheory
