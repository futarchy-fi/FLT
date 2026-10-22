/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorIntersection
public import FLT.Mazur.IdealTensorAdicImage
public import FLT.Mazur.AdicDiscrepancySeparation
public import Mathlib.RingTheory.Flat.Tensor

/-!
# The Artin-Rees step of the local flatness criterion

For a module finite over a local Noetherian target, injectivity on ideals
containing positive powers of one base ideal implies full flatness. The
extended ideal must be proper. No module finiteness over the base is used.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorAdicCriterion
open ModuleIdealTensor
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S] [Module.Finite S M]

/-- Artin-Rees and local separation eliminate a kernel tested modulo all positive powers. -/
theorem inclusion_injective (A : Ideal R) (hA : A.map (algebraMap R S) ≠ ⊤)
    (J : Ideal R)
    (h : ∀ n : ℕ, Function.Injective (inclusion (S := S) (M := M) (J ⊔ A ^ (n + 1)))) :
    Function.Injective (inclusion (S := S) (M := M) J) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  let _ := tensor_finite (S := S) (M := M) J J.fg_of_isNoetherianRing
  apply AdicDiscrepancySeparation.eq_zero_of_local (A.map (algebraMap R S)) hA z
  intro n
  obtain ⟨c, hc⟩ := A.exists_pow_inf_eq_pow_smul J
  have he := hc (n + 1 + c) (Nat.le_add_left c (n + 1))
  rw [Nat.add_sub_cancel] at he
  have hle : J ⊓ A ^ (n + 1 + c) ≤ A ^ (n + 1) • J := by
    have hb := smul_mono_right (A ^ (n + 1))
      (show A ^ c • ⊤ ⊓ J ≤ J from inf_le_right)
    rw [← he] at hb
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top, inf_comm] using hb
  obtain ⟨w, hw⟩ := IdealTensorIntersection.kernel_lifts_inf J (A ^ (n + 1 + c))
    (by rw [show n + 1 + c = n + c + 1 by omega]; exact h (n + c)) z hz
  rw [← hw, ← Ideal.map_pow]
  exact IdealTensorAdicImage.inclusion_mem (A ^ (n + 1)) J _ inf_le_left hle w

/-- All positive thickening tests suffice for flatness over the original base. -/
theorem flat_of_adic_tests (A : Ideal R) (hA : A.map (algebraMap R S) ≠ ⊤)
    (h : ∀ (J : Ideal R) (n : ℕ),
      Function.Injective (inclusion (S := S) (M := M) (J ⊔ A ^ (n + 1)))) :
    Module.Flat R M := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro J
  apply (J.subtype.lTensor_inj_iff_rTensor_inj M).mp
  intro x y hxy
  apply inclusion_injective A hA J (h J)
  exact congrArg (AlgebraTensorModule.rid R S M) hxy

end FLT.Mazur.IdealTensorAdicCriterion
