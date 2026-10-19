/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelGaloisLabels
public import FLT.GroupScheme.FiniteFlat

/-!
# The rational finite etale algebra of the actual source kernel

Equivariant functions use the transported source Galois action, rather than
constant functions on rational labels. The algebra has rank p and its Hopf
operations come from the actual kernel addition. Its embedding into the rational
source curve still requires geometric descent of the closed immersion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- Functions on the retained labels equivariant for the actual source Galois action. -/
def PrimeKernelDescentAlgebra : Type :=
  letI := primeKernelLabelAction E p q hq hfixed
  ZMod p →[Field.absoluteGaloisGroup ℚ] AlgebraicClosure ℚ

instance primeKernelDescentAlgebraCommRing :
    CommRing (PrimeKernelDescentAlgebra E p q hq hfixed) := by
  unfold PrimeKernelDescentAlgebra
  infer_instance

instance primeKernelDescentAlgebraAlgebra :
    Algebra ℚ (PrimeKernelDescentAlgebra E p q hq hfixed) := by
  unfold PrimeKernelDescentAlgebra
  infer_instance

instance primeKernelDescentAlgebra_finite :
    Module.Finite ℚ (PrimeKernelDescentAlgebra E p q hq hfixed) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  exact inferInstanceAs
    (Module.Finite ℚ (ZMod p →[Field.absoluteGaloisGroup ℚ] AlgebraicClosure ℚ))

instance primeKernelDescentAlgebra_etale :
    Algebra.Etale ℚ (PrimeKernelDescentAlgebra E p q hq hfixed) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  exact inferInstanceAs
    (Algebra.Etale ℚ (ZMod p →[Field.absoluteGaloisGroup ℚ] AlgebraicClosure ℚ))

/-- The rational coordinate algebra has exactly the original prime rank. -/
theorem primeKernelDescentAlgebra_finrank :
    Module.finrank ℚ (PrimeKernelDescentAlgebra E p q hq hfixed) = p := by
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  exact (GaloisModule.finrank_equivariantFunctions ℚ (AlgebraicClosure ℚ) (ZMod p)).trans
    (Nat.card_zmod p)

/-- Kernel addition constructs the rational Hopf operations on the equivariant functions. -/
@[instance_reducible] def primeKernelDescentHopfAlgebra :
    HopfAlgebra ℚ (PrimeKernelDescentAlgebra E p q hq hfixed) := by
  letI := primeKernelLabelAction E p q hq hfixed
  letI := primeKernelLabelAction_continuous E p q hq hfixed
  exact GaloisModule.GenericFiber.hopfAlgebra ℚ (AlgebraicClosure ℚ) (ZMod p)

/-- Evaluation at an original kernel label is an actual geometric point of the rational algebra. -/
def primeKernelDescentEvaluation (i : ZMod p) :
    PrimeKernelDescentAlgebra E p q hq hfixed →ₐ[ℚ] AlgebraicClosure ℚ := by
  letI := primeKernelLabelAction E p q hq hfixed
  exact MulActionHom.evalAlgHom (Field.absoluteGaloisGroup ℚ) ℚ (ZMod p)
    (AlgebraicClosure ℚ) i

/-- These evaluations exhaust the geometric points of the rational descended algebra. -/
theorem primeKernelDescentEvaluation_bijective :
    Function.Bijective (primeKernelDescentEvaluation E p q hq hfixed) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  exact InfiniteGalois.evalAlgHom_bijective ℚ (AlgebraicClosure ℚ) (ZMod p)

/-- Evaluation retains the actual, possibly nontrivial, Galois permutation of source labels. -/
theorem primeKernelDescentEvaluation_galois (g : Field.absoluteGaloisGroup ℚ)
    (i : ZMod p) (a : PrimeKernelDescentAlgebra E p q hq hfixed) :
    primeKernelDescentEvaluation E p q hq hfixed
      (primeKernelLabelGalois E p q hq hfixed g i) a =
        g (primeKernelDescentEvaluation E p q hq hfixed i a) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  exact a.map_smul' g i

end WeierstrassCurve.Velu
