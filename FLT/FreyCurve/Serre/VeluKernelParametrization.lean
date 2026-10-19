/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluPrimeKernel

/-!
# A retained parametrization of the geometric source kernel

Choose the proved exact line once. Its inclusion into the original affine
curve has precisely the actual torsion quotient kernel as its range.
-/

@[expose] public noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)

/-- A chosen exact-line equivalence with the original geometric source kernel. -/
def primeKernelParamEquiv : ZMod p ≃+ torsionKernel E p q := Classical.choice <| by
  obtain ⟨i, hi, hex⟩ := exists_exact_torsionKernel_line E p q hq
  exact ⟨torsionKernelEquivOfExact E p q i hi hex⟩

/-- The original kernel embedded into the original source affine point group. -/
def primeKernelParam : ZMod p →+ (E⁄(AlgebraicClosure ℚ)).Point :=
  (torsionKernel E p q).subtype.comp (primeKernelParamEquiv E p q hq).toAddMonoidHom

/-- The retained kernel labels are all distinct. -/
theorem primeKernelParam_injective : Function.Injective (primeKernelParam E p q hq) :=
  Subtype.val_injective.comp (primeKernelParamEquiv E p q hq).injective

/-- The parametrization covers precisely the original geometric source kernel. -/
theorem primeKernelParam_range : (primeKernelParam E p q hq).range = torsionKernel E p q := by
  ext P
  constructor
  · rintro ⟨i, rfl⟩
    exact (primeKernelParamEquiv E p q hq i).property
  · intro hP
    obtain ⟨i, hi⟩ := (primeKernelParamEquiv E p q hq).surjective ⟨P, hP⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- The chosen component one has exact order p in the original source curve. -/
theorem primeKernelParam_one_order : addOrderOf (primeKernelParam E p q hq 1) = p :=
  (addOrderOf_injective _ (primeKernelParam_injective E p q hq) 1).trans
    (ZMod.addOrderOf_one p)

/-- Every label retains the original prime-torsion relation. -/
theorem primeKernelParam_killed (i : ZMod p) : p • primeKernelParam E p q hq i = 0 :=
  torsionKernel_killed E p q _ (primeKernelParamEquiv E p q hq i).property

end WeierstrassCurve.Velu
