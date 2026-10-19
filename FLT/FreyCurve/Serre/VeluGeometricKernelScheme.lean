/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelParametrization
public import FLT.Mazur.AffineCyclicClosedSubgroup

/-!
# The actual geometric source kernel as a finite closed subgroup scheme

The subgroup lies on the original source cubic over Qbar. Its rank is p,
and its component sections are exactly the original torsion quotient kernel.
This construction does not identify the source kernel with target rational torsion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)

/-- The actual source curve's geometric finite closed subgroup of rank p. -/
def primeKernelClosedSubgroup :
    (integralGeneralizedEllipticCurve (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).isUnit_Δ).FiniteSubgroup p :=
  affineCyclicClosedSubgroup _ (primeKernelParam E p q hq)
    (primeKernelParam_injective E p q hq)

/-- The constructed geometric source kernel is etale. -/
theorem primeKernelClosedSubgroup_etale :
    Etale (primeKernelClosedSubgroup E p q hq).carrier.hom :=
  affineCyclicClosedSubgroup_etale _ _ _

/-- Its degree is p at every geometric base point, as a finite locally free scheme. -/
theorem primeKernelClosedSubgroup_rank (s : Spec (.of (AlgebraicClosure ℚ))) :
    (primeKernelClosedSubgroup E p q hq).carrier.hom.finrank s = p :=
  (primeKernelClosedSubgroup E p q hq).finrank s

/-- Each component lands at the original geometric source-kernel point. -/
theorem primeKernelClosedSubgroup_component (i : ZMod p) :
    ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i ≫
      (primeKernelClosedSubgroup E p q hq).inclusion =
        (affineRationalGroupSectionAddHom (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (primeKernelParam E p q hq i)).toMul :=
  affineCyclicClosedSubgroup_component _ _ _ i

/-- The component sections are exactly the actual source quotient kernel. -/
theorem primeKernelClosedSubgroup_mem (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    (∃ i : ZMod p, ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i ≫
      (primeKernelClosedSubgroup E p q hq).inclusion =
        (affineRationalGroupSectionAddHom (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) P).toMul)
      ↔ P ∈ torsionKernel E p q := by
  rw [← primeKernelParam_range E p q hq]
  exact affineCyclicClosedSubgroup_mem
    (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) _ _ P

/-- The actual closed ideal is the product of the original source-kernel point ideals. -/
theorem primeKernelClosedSubgroup_kernel :
    (primeKernelClosedSubgroup E p q hq).inclusion.left.ker =
      ∏ i : ZMod p,
        ((affineRationalGroupSectionAddHom (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (primeKernelParam E p q hq i)).toMul).left.ker :=
  affineCyclicClosedSubgroup_kernel _ _ _

end WeierstrassCurve.Velu
