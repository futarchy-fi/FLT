/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConnectedTensorPoint
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Connectedness of the three-adic cube-root group

In every residue field of `ℤ_[3][ℤ/3]`, the group elements become one:
`(g - 1)^3 = 0` in characteristic three. Hence the augmentation ideal lies
in the Jacobson radical and the only integral idempotents are zero and one.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- The standard coordinate algebra of the group of cube roots of unity over `ℤ_[3]`. -/
abbrev PadicMuThreeAlgebra := MonoidAlgebra ℤ_[3] (Multiplicative (ZMod 3))

/-- Every group element in the cube-root coordinate algebra has cube one. -/
theorem muThree_group_cube (g : Multiplicative (ZMod 3)) : g ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  change (3 : ℕ) • g.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- A field-valued point in characteristic three kills every `g - 1`. -/
theorem muThree_single_eq_one_in_char_three {L : Type*} [Field L] [CharP L 3]
    (f : PadicMuThreeAlgebra →+* L) (g : Multiplicative (ZMod 3)) :
    f (MonoidAlgebra.single g 1) = 1 := by
  have hp : (f (MonoidAlgebra.single g 1) - 1) ^ 3 = 0 := by
    rw [sub_pow_char, ← map_pow, MonoidAlgebra.single_pow, muThree_group_cube,
      one_pow, ← MonoidAlgebra.one_def, map_one, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hp)

/-- The augmentation ideal of the three-adic cube-root group is Jacobson. -/
theorem padicMuThree_counit_ker_le_jacobson :
    RingHom.ker (Bialgebra.counitAlgHom ℤ_[3] PadicMuThreeAlgebra).toRingHom ≤
      (⊥ : Ideal PadicMuThreeAlgebra).jacobson := by
  intro x hx
  apply Submodule.mem_sInf.mpr
  rintro m ⟨_, hm⟩
  let := hm
  let : Field (PadicMuThreeAlgebra ⧸ m) := Ideal.Quotient.field m
  have hmR := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[3]) m
  have hthree : (3 : PadicMuThreeAlgebra) ∈ m := by
    have h : (3 : ℤ_[3]) ∈ Ideal.under ℤ_[3] m := by
      rw [IsLocalRing.eq_maximalIdeal hmR, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span (Set.mem_singleton _)
    change algebraMap ℤ_[3] PadicMuThreeAlgebra (3 : ℤ_[3]) ∈ m at h
    rwa [map_ofNat] at h
  let : CharP (PadicMuThreeAlgebra ⧸ m) 3 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk m) 3]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hthree)
  let ε := Bialgebra.counitAlgHom ℤ_[3] PadicMuThreeAlgebra
  have hf : Ideal.Quotient.mk m = (algebraMap ℤ_[3] (PadicMuThreeAlgebra ⧸ m)).comp
      ε.toRingHom := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [ε]
      rfl
    · intro g
      simp [ε, muThree_single_eq_one_in_char_three (Ideal.Quotient.mk m) g]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hf]
  change algebraMap ℤ_[3] (PadicMuThreeAlgebra ⧸ m) (ε x) = 0
  rw [show ε x = 0 from hx, map_zero]

/-- The cube-root group over the three-adic integers is connected. -/
theorem padicMuThree_idempotent_trivial (d : PadicMuThreeAlgebra)
    (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  let ε := (Bialgebra.counitAlgHom ℤ_[3] PadicMuThreeAlgebra).toRingHom
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hd.map ε) with h | h
  · left
    apply idempotent_eq_of_map_eq ε padicMuThree_counit_ker_le_jacobson hd .zero
    simpa only [map_zero] using h
  · right
    apply idempotent_eq_of_map_eq ε padicMuThree_counit_ker_le_jacobson hd .one
    simpa only [map_one] using h

end ThreeAdicPlan
