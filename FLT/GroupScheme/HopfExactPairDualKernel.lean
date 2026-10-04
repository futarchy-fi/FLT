/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfExactPairAnnihilator
public import FLT.GroupScheme.RaynaudFlatKernelExactness

/-! # Perfect pairing with the actual dual augmentation quotient -/

@[expose] public noncomputable section
open scoped TensorProduct
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

/-- The scheme-theoretic kernel ring of the actual dual quotient. -/
abbrev DualKernel := CartierDual R H ⧸ augmentationIdeal (bialgMap i)

include hi in
/-- Relative faithful flatness makes the dual kernel ring flat over the integral base. -/
theorem dualKernel_flat : Module.Flat R (DualKernel i) := by
  let := (bialgMap i).toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R (CartierDual R A) (CartierDual R H) :=
    IsScalarTower.of_algHom (bialgMap i).toAlgHom
  let : Module.FaithfullyFlat (CartierDual R A) (CartierDual R H) :=
    bialgMap_faithfullyFlat_of_surjective i hi
  exact (Bialgebra.counitAlgHom R (CartierDual R A)).quotient_map_ker_flat

/-- The original transpose descends to the actual dual augmentation quotient. -/
def dualKernelMap : DualKernel i →ₐ[R] CartierDual R Q :=
  Ideal.Quotient.liftₐ _ (bialgMap q).toAlgHom (dualAugmentationIdeal_le_ker i q hi hk)

/-- Original quotient coordinates pair with the actual dual kernel ring. -/
def dualKernelPairing : Q →ₗ[R] Module.Dual R (DualKernel i) :=
  (dualKernelMap i q hi hk).toLinearMap.dualMap.comp
    ((linearEquiv (R := R) (A := Q)).toLinearMap.dualMap.comp (Module.Dual.eval R Q))

omit [IsDomain R] [IsPrincipalIdealRing R] [Coalgebra.IsCocomm R Q] in
/-- The descended pairing is evaluation on the original quotient coordinates. -/
@[simp] theorem dualKernelPairing_mk (b : Q) (φ : CartierDual R H) :
    dualKernelPairing i q hi hk b (Ideal.Quotient.mk _ φ) = φ (q b) := rfl

omit [IsDomain R] [IsPrincipalIdealRing R] [Coalgebra.IsCocomm R Q] in
/-- Descent and integral biduality prove perfection of this pairing. -/
theorem dualKernelPairing_bijective (hq : q.toAlgHom.toRingHom.FaithfullyFlat) :
    Function.Bijective (dualKernelPairing i q hi hk) := by
  let J := augmentationIdeal (bialgMap i)
  let π := Ideal.Quotient.mkₐ R J
  constructor
  · intro b b' hb
    apply hq.injective
    apply (Module.evalEquiv R H).injective
    ext φ
    exact congrArg (fun l : Module.Dual R (DualKernel i) ↦ l (π (WithConv.toConv φ))) hb
  · intro l
    let lH : Module.Dual R (CartierDual R H) := l.comp π.toLinearMap
    obtain ⟨h, hh⟩ := (bidualLinearEquiv (R := R) (A := H)).surjective (WithConv.toConv lH)
    have heval (φ : CartierDual R H) : φ h = l (π φ) :=
      congrArg (fun k : CartierDual R (CartierDual R H) ↦ k φ) hh
    obtain ⟨b, hb⟩ := exists_preimage_of_annihilates i q hi hk hq h (fun φ hφ ↦ by
      rw [heval]
      have hz : π φ = 0 := (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr hφ
      rw [hz, map_zero])
    refine ⟨b, ?_⟩
    apply LinearMap.ext
    intro c
    obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective c
    change φ (q b) = l (π φ)
    rw [hb]
    exact heval φ

end HopfAlgebra.ExactPair
