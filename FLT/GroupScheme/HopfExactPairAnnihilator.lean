/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfExactPair
public import FLT.GroupScheme.CartierDualSurjection

/-! # The annihilator of the actual dual augmentation ideal -/

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

omit [IsDomain R] [IsPrincipalIdealRing R] [Coalgebra.IsCocomm R A]
  [Coalgebra.IsCocomm R H] [Coalgebra.IsCocomm R Q] in
include hi hk in
/-- The transposed composite is zero, with the original integral counits. -/
theorem dualCompositionZero : (bialgMap q).toAlgHom.comp (bialgMap i).toAlgHom =
    (Algebra.ofId R (CartierDual R Q)).comp
      (Bialgebra.counitAlgHom R (CartierDual R A)) := by
  ext φ b
  change φ (i (q b)) = φ 1 * Coalgebra.counit (R := R) b
  have hb := AlgHom.congr_fun (compositionZero i q hi hk) b
  change i (q b) = algebraMap R A (Coalgebra.counit b) at hb
  rw [hb, Algebra.algebraMap_eq_smul_one]
  change φ.ofConv (Coalgebra.counit (R := R) b • (1 : A)) = _
  rw [map_smul, smul_eq_mul, mul_comm]

omit [IsDomain R] [IsPrincipalIdealRing R] [Coalgebra.IsCocomm R Q] in
include hi hk in
/-- The transposed quotient annihilates the generated dual augmentation ideal. -/
theorem dualAugmentationIdeal_le_ker : augmentationIdeal (bialgMap i) ≤
    RingHom.ker (bialgMap q).toAlgHom.toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro φ hφ
  change bialgMap q (bialgMap i φ) = 0
  have he := AlgHom.congr_fun (dualCompositionZero i q hi hk) φ
  change bialgMap q (bialgMap i φ) =
    algebraMap R (CartierDual R Q) (Bialgebra.counitAlgHom R (CartierDual R A) φ) at he
  change Bialgebra.counitAlgHom R (CartierDual R A) φ = 0 at hφ
  simpa only [hφ, map_zero] using he

omit [IsDomain R] [IsPrincipalIdealRing R] [Coalgebra.IsCocomm R Q]
  [Module.Finite R Q] [Module.Projective R Q] in
include hi hk in
/-- Annihilating the dual augmentation ideal forces descent to the original quotient. -/
theorem exists_preimage_of_annihilates (hq : q.toAlgHom.toRingHom.FaithfullyFlat)
    (h : H) (hh : ∀ φ : CartierDual R H, φ ∈ augmentationIdeal (bialgMap i) → φ h = 0) :
    ∃ b, q b = h := by
  let := q.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q H := IsScalarTower.of_algHom q.toAlgHom
  let : Module.FaithfullyFlat Q H := hq
  apply (exists_preimage_iff i q hi hk rfl h).mpr
  apply tensor_eq_of_forall_pairing
  intro φ ψ
  rw [tensor_pairing_coaction, tensorEquiv_tmul]
  let ψ₀ : CartierDual R A := ψ - ψ 1 • 1
  have hψ₀ : ψ₀ ∈ RingHom.ker
      (Bialgebra.counitAlgHom R (CartierDual R A)).toRingHom := by
    change ψ₀ 1 = 0
    simp [ψ₀]
  have hm := hh (φ * bialgMap i ψ₀)
    (Ideal.mul_mem_left _ φ (Ideal.mem_map_of_mem _ hψ₀))
  have he : φ * bialgMap i ψ₀ = φ * bialgMap i ψ - ψ 1 • φ := by
    simp [ψ₀, mul_sub]
  rw [he] at hm
  change (φ * bialgMap i ψ) h - ψ 1 * φ h = 0 at hm
  exact (sub_eq_zero.mp hm).trans (mul_comm _ _)

end HopfAlgebra.ExactPair
