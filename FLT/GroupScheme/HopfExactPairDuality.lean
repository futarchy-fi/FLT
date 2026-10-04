/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfExactPairDualKernel

/-! # Cartier duality reverses actual integral augmentation-kernel sequences -/

@[expose] public noncomputable section
namespace HopfAlgebra.ExactPair
open CartierDual
variable {R A H Q : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [CommRing H] [CommRing Q]
  [HopfAlgebra R A] [HopfAlgebra R H] [HopfAlgebra R Q]
  [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R H] [Coalgebra.IsCocomm R Q]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R H] [Module.Projective R H]
  [Module.Finite R Q] [Module.Projective R Q]
  (i : H →ₐc[R] A) (q : Q →ₐc[R] H) (hi : Function.Surjective i)
  (hk : augmentationIdeal q = RingHom.ker i.toAlgHom.toRingHom)
  (hq : q.toAlgHom.toRingHom.FaithfullyFlat)

/-- Integral biduality identifies the dual kernel with the original quotient's dual. -/
def dualKernelLinearEquiv : DualKernel i ≃ₗ[R] CartierDual R Q := by
  let := dualKernel_flat i hi
  let : Module.FinitePresentation R (DualKernel i) :=
    Module.finitePresentation_of_finite R (DualKernel i)
  let : Module.Projective R (DualKernel i) := Module.Flat.projective_of_finitePresentation
  let e := LinearEquiv.ofBijective (dualKernelPairing i q hi hk)
    (dualKernelPairing_bijective i q hi hk hq)
  exact (Module.evalEquiv R (DualKernel i)).trans (e.dualMap.trans linearEquiv.symm)

omit [Coalgebra.IsCocomm R Q] in
/-- This equivalence is the actual transposed quotient on representatives. -/
@[simp] theorem dualKernelLinearEquiv_mk (φ : CartierDual R H) :
    dualKernelLinearEquiv i q hi hk hq (Ideal.Quotient.mk _ φ) = bialgMap q φ := rfl

/-- The algebra equivalence with the actual dual kernel uses the given transpose. -/
def dualKernelEquiv : DualKernel i ≃ₐ[R] CartierDual R Q :=
  AlgEquiv.ofBijective (dualKernelMap i q hi hk) (by
    have he : (dualKernelMap i q hi hk : DualKernel i → CartierDual R Q) =
        dualKernelLinearEquiv i q hi hk hq := by
      funext c
      obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective c
      rfl
    rw [he]
    exact (dualKernelLinearEquiv i q hi hk hq).bijective)

omit [Coalgebra.IsCocomm R Q] in
include hi hk hq in
/-- The actual dual augmentation-kernel equation. -/
theorem dual_kernel : augmentationIdeal (bialgMap i) =
    RingHom.ker (bialgMap q).toAlgHom.toRingHom := by
  ext φ
  change φ ∈ augmentationIdeal (bialgMap i) ↔ bialgMap q φ = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (dualKernelLinearEquiv i q hi hk hq).map_eq_zero_iff.symm

omit [Coalgebra.IsCocomm R Q] in
include i hi hk hq in
/-- The transposed original quotient is a closed inclusion on dual group schemes. -/
theorem dual_closed : Function.Surjective (bialgMap q) := by
  intro ψ
  obtain ⟨c, hc⟩ := (dualKernelLinearEquiv i q hi hk hq).surjective ψ
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨φ, hc⟩

end HopfAlgebra.ExactPair
