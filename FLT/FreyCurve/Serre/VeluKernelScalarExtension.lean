/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelDescentAlgebra
public import FLT.GroupScheme.EquivariantScalarExtension

/-!
# Scalar extension of the actual rational source-kernel algebra

The coordinate comparison preserves every original evaluation, including its
Galois action. It constructs the full product-coordinate algebra over Qbar.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- Scalar extension gives exactly the product coordinates of the geometric kernel. -/
def primeKernelScalarEquiv :
    AlgebraicClosure ℚ ⊗[ℚ] PrimeKernelDescentAlgebra E p q hq hfixed ≃ₐ[AlgebraicClosure ℚ]
      (ZMod p → AlgebraicClosure ℚ) := by
  letI := primeKernelLabelAction E p q hq hfixed
  letI := primeKernelLabelAction_continuous E p q hq hfixed
  exact GaloisModule.scalarExtensionEquiv ℚ (AlgebraicClosure ℚ) (ZMod p)

/-- Each pure tensor evaluates at the same original label. -/
@[simp] theorem primeKernelScalarEquiv_tmul (r : AlgebraicClosure ℚ)
    (a : PrimeKernelDescentAlgebra E p q hq hfixed) (i : ZMod p) :
    primeKernelScalarEquiv E p q hq hfixed (r ⊗ₜ[ℚ] a) i =
      r * primeKernelDescentEvaluation E p q hq hfixed i a := rfl

/-- The coordinate comparison extends the original geometric evaluation maps. -/
theorem primeKernelScalarEquiv_evaluation (i : ZMod p) :
    (Pi.evalAlgHom (AlgebraicClosure ℚ) (fun _ : ZMod p ↦ AlgebraicClosure ℚ) i).comp
      (primeKernelScalarEquiv E p q hq hfixed).toAlgHom =
        Algebra.TensorProduct.liftEquivRight ℚ (AlgebraicClosure ℚ) _ _
          (primeKernelDescentEvaluation E p q hq hfixed i) := rfl

/-- Restriction to rational coefficients retains the actual source Galois action. -/
theorem primeKernelScalarEquiv_galois (g : Field.absoluteGaloisGroup ℚ)
    (a : PrimeKernelDescentAlgebra E p q hq hfixed) (i : ZMod p) :
    primeKernelScalarEquiv E p q hq hfixed (1 ⊗ₜ[ℚ] a)
        (primeKernelLabelGalois E p q hq hfixed g i) =
      g (primeKernelScalarEquiv E p q hq hfixed (1 ⊗ₜ[ℚ] a) i) := by
  simp only [primeKernelScalarEquiv_tmul, one_mul]
  exact primeKernelDescentEvaluation_galois E p q hq hfixed g i a

end WeierstrassCurve.Velu
