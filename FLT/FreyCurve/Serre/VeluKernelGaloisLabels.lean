/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelParametrization

/-!
# Galois permutations of the retained source-kernel labels

The action on labels is transported from the actual source points. It need
not fix the labels, and thus does not assert that this subgroup is rationally split.
-/

@[expose] public noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- Restrict the actual source Galois action to its stable geometric kernel. -/
def torsionKernelGaloisEquiv (g : Field.absoluteGaloisGroup ℚ) :
    torsionKernel E p q ≃+ torsionKernel E p q where
  toFun P := ⟨g • P.val, torsionKernel_stable E p q hfixed g P.val P.property⟩
  invFun P := ⟨g⁻¹ • P.val, torsionKernel_stable E p q hfixed g⁻¹ P.val P.property⟩
  left_inv P := Subtype.ext (inv_smul_smul g P.val)
  right_inv P := Subtype.ext (smul_inv_smul g P.val)
  map_add' P Q := Subtype.ext (smul_add g P.val Q.val)

/-- Transport the original action to the selected cyclic coordinates. -/
def primeKernelLabelGalois (g : Field.absoluteGaloisGroup ℚ) : ZMod p ≃+ ZMod p :=
  ((primeKernelParamEquiv E p q hq).trans (torsionKernelGaloisEquiv E p q hfixed g)).trans
    (primeKernelParamEquiv E p q hq).symm

/-- The action on labels recovers the actual Galois-conjugate source point. -/
theorem primeKernelLabelGalois_point (g : Field.absoluteGaloisGroup ℚ) (i : ZMod p) :
    primeKernelParam E p q hq (primeKernelLabelGalois E p q hq hfixed g i) =
      g • primeKernelParam E p q hq i := by
  change ((primeKernelParamEquiv E p q hq)
    ((primeKernelParamEquiv E p q hq).symm _)).val = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Identity Galois conjugation fixes the retained labels. -/
theorem primeKernelLabelGalois_one : primeKernelLabelGalois E p q hq hfixed 1 =
    AddEquiv.refl (ZMod p) := by
  ext i
  apply primeKernelParam_injective E p q hq
  rw [primeKernelLabelGalois_point, one_smul]
  rfl

/-- Galois multiplication acts by composition on the actual kernel labels. -/
theorem primeKernelLabelGalois_mul (g h : Field.absoluteGaloisGroup ℚ) (i : ZMod p) :
    primeKernelLabelGalois E p q hq hfixed (g * h) i =
      primeKernelLabelGalois E p q hq hfixed g
        (primeKernelLabelGalois E p q hq hfixed h i) := by
  apply primeKernelParam_injective E p q hq
  rw [primeKernelLabelGalois_point, primeKernelLabelGalois_point,
    primeKernelLabelGalois_point, mul_smul]

/-- The actual continuous Galois action on the finite cyclic label group. -/
@[instance_reducible] def primeKernelLabelAction :
    DistribMulAction (Field.absoluteGaloisGroup ℚ) (ZMod p) where
  smul g i := primeKernelLabelGalois E p q hq hfixed g i
  one_smul i := congrArg (fun e : ZMod p ≃+ ZMod p ↦ e i)
    (primeKernelLabelGalois_one E p q hq hfixed)
  mul_smul g h i := primeKernelLabelGalois_mul E p q hq hfixed g h i
  smul_zero g := (primeKernelLabelGalois E p q hq hfixed g).map_zero
  smul_add g i j := (primeKernelLabelGalois E p q hq hfixed g).map_add i j

/-- Discrete continuity is inherited from the actual algebraic source points. -/
theorem primeKernelLabelAction_continuous :
    letI := primeKernelLabelAction E p q hq hfixed
    ContinuousSMulDiscrete (Field.absoluteGaloisGroup ℚ) (ZMod p) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  constructor
  intro i j
  have he : {g : Field.absoluteGaloisGroup ℚ | g • i = j} =
      {g | g • primeKernelParam E p q hq i = primeKernelParam E p q hq j} := by
    ext g
    change g • i = j ↔ g • primeKernelParam E p q hq i = primeKernelParam E p q hq j
    rw [← primeKernelLabelGalois_point E p q hq hfixed]
    exact (primeKernelParam_injective E p q hq).eq_iff.symm
  rw [he]
  exact ContinuousSMulDiscrete.isOpen_smul_eq _ _ _

end WeierstrassCurve.Velu
