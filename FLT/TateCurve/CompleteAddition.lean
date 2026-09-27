/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Addition
public import FLT.TateCurve.Fibers
public import FLT.TateCurve.QuotientAvoidance

/-!
# The full Tate addition law

An auxiliary parameter avoids the finitely many equalities responsible for
colliding abscissae. Three applications of generic addition, followed by
cancellation, prove addition for the original pair.
-/

@[expose] public section

open ValuativeRel Filter

namespace TateCurve

section Groups

variable {G A : Type*} [CommGroup G] [AddCommGroup A]

/-- The six exclusions needed for three distinct nonidentity abscissae. -/
private def GenericPair (a b : G) : Prop :=
  a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 ∧ a ≠ b ∧ a ^ 2 * b ≠ 1 ∧ a * b ^ 2 ≠ 1

/-- For a fixed nonidentity argument, generic partners form a cofinite set. -/
private theorem eventually_genericPair
    (hsq : ∀ a : G, {b : G | b ^ 2 = a}.Finite) {a : G} (ha : a ≠ 1) :
    ∀ᶠ b in cofinite, GenericPair a b := by
  have hs : ∀ᶠ b in cofinite, b ^ 2 ≠ a⁻¹ := (hsq a⁻¹).compl_mem_cofinite
  filter_upwards [eventually_cofinite_ne (1 : G), eventually_cofinite_ne a⁻¹,
    eventually_cofinite_ne a, eventually_cofinite_ne (a ^ 2)⁻¹, hs] with b hb hi he h2 hs
  refine ⟨ha, hb, ?_, he.symm, ?_, ?_⟩
  · exact fun h ↦ hi (eq_inv_of_mul_eq_one_right h)
  · exact fun h ↦ h2 (eq_inv_of_mul_eq_one_right h)
  · exact fun h ↦ hs (eq_inv_of_mul_eq_one_right h)

/-- Generic multiplicativity extends to every nonexceptional pair by one auxiliary argument. -/
private theorem map_mul_of_generic [Infinite G]
    (hsq : ∀ a : G, {b : G | b ^ 2 = a}.Finite) (f : G → A)
    (hf : ∀ a b, GenericPair a b → f (a * b) = f a + f b)
    (a b : G) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a * b ≠ 1) :
    f (a * b) = f a + f b := by
  have h1 := eventually_genericPair hsq ha
  have h2 : ∀ᶠ w in cofinite, GenericPair b (a * w) :=
    (Equiv.mulLeft a).injective.tendsto_cofinite (eventually_genericPair hsq hb)
  have h3 := eventually_genericPair hsq hab
  obtain ⟨w, hw1, hw2, hw3⟩ := (h1.and (h2.and h3)).exists
  apply add_right_cancel (b := f w)
  calc f (a * b) + f w = f ((a * b) * w) := (hf _ _ hw3).symm
    _ = f (b * (a * w)) := congrArg f (by ac_rfl)
    _ = f b + f (a * w) := hf _ _ hw2
    _ = (f a + f b) + f w := by rw [hf _ _ hw1]; abel

end Groups

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]

/-- Generic quotient pairs satisfy the Tate addition law by the abscissa fiber theorem. -/
private theorem quotientPoint_mul_of_generic (q : Kˣ) (hq : valuation K (q : K) < 1)
    (a b : Kˣ ⧸ Subgroup.zpowers q) (hg : GenericPair a b) :
    quotientPoint q hq (a * b) = quotientPoint q hq a + quotientPoint q hq b := by
  induction a using Quotient.inductionOn with
  | h u =>
    induction b using Quotient.inductionOn with
    | h v =>
      obtain ⟨hu, hv, huv, hne, huuv, huvv⟩ := hg
      have hum : u ∉ Subgroup.zpowers q := fun h ↦ hu ((QuotientGroup.eq_one_iff u).mpr h)
      have hvm : v ∉ Subgroup.zpowers q := fun h ↦ hv ((QuotientGroup.eq_one_iff v).mpr h)
      have huvm : u * v ∉ Subgroup.zpowers q := fun h ↦
        huv (by simpa only [QuotientGroup.mk_mul] using (QuotientGroup.eq_one_iff (u * v)).mpr h)
      change uniformizationPoint q hq (u * v) =
        uniformizationPoint q hq u + uniformizationPoint q hq v
      apply uniformizationPoint_mul_of_distinct_tateX q hq u v hum hvm huvm
      · intro h
        rcases (tateX_eq_iff_quotient q u v hq hum hvm).mp h with h | h
        · exact hne h
        · exact huv (mul_eq_one_iff_eq_inv.mpr h)
      · intro h
        rcases (tateX_eq_iff_quotient q (u * v) u hq huvm hum).mp h with h | h
        · apply hv
          have he : (u : Kˣ ⧸ Subgroup.zpowers q) * v = u := h
          exact mul_left_cancel (by simpa only [mul_one] using he)
        · apply huuv
          have he : ((u : Kˣ ⧸ Subgroup.zpowers q) * v) * u = 1 :=
            mul_eq_one_iff_eq_inv.mpr h
          simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using he
      · intro h
        rcases (tateX_eq_iff_quotient q (u * v) v hq huvm hvm).mp h with h | h
        · apply hu
          have he : (u : Kˣ ⧸ Subgroup.zpowers q) * v = v := h
          exact mul_right_cancel (by simpa only [one_mul] using he)
        · apply huvv
          have he : ((u : Kˣ ⧸ Subgroup.zpowers q) * v) * v = 1 :=
            mul_eq_one_iff_eq_inv.mpr h
          simpa only [pow_two, mul_assoc] using he

/-- Multiplication of Tate parameters becomes addition of points, including all collisions. -/
theorem uniformizationPoint_mul (q : Kˣ) (hq : valuation K (q : K) < 1) (u v : Kˣ) :
    uniformizationPoint q hq (u * v) =
      uniformizationPoint q hq u + uniformizationPoint q hq v := by
  apply uniformizationPoint_mul_of_nonexceptional q hq _ u v
  intro u v hu hv huv
  let : Infinite (Kˣ ⧸ Subgroup.zpowers q) := infinite_quotient q hq
  exact map_mul_of_generic (finite_quotient_square_fiber q) (quotientPoint q hq)
    (quotientPoint_mul_of_generic q hq) (u : Kˣ ⧸ Subgroup.zpowers q) v
    (fun h ↦ hu ((QuotientGroup.eq_one_iff u).mp h))
    (fun h ↦ hv ((QuotientGroup.eq_one_iff v).mp h))
    (fun h ↦ huv ((QuotientGroup.eq_one_iff (u * v)).mp h))

/-- The descended Tate point map respects multiplication. -/
theorem quotientPoint_mul (q : Kˣ) (hq : valuation K (q : K) < 1)
    (u v : Kˣ ⧸ Subgroup.zpowers q) :
    quotientPoint q hq (u * v) = quotientPoint q hq u + quotientPoint q hq v := by
  induction u using Quotient.inductionOn with
  | h u =>
    induction v using Quotient.inductionOn with
    | h v => exact uniformizationPoint_mul q hq u v

/-- The Tate point map on the multiplicative quotient, as an additive homomorphism. -/
noncomputable def quotientPointHom (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Additive (Kˣ ⧸ Subgroup.zpowers q) →+
      (WeierstrassCurve.tateCurve (q : K)).toAffine.Point where
  toFun u := quotientPoint q hq u.toMul
  map_zero' := (quotientPoint_eq_zero q hq 1).mpr rfl
  map_add' := quotientPoint_mul q hq

/-- The Tate homomorphism is injective because only the identity class maps to infinity. -/
theorem quotientPointHom_injective (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Function.Injective (quotientPointHom q hq) := by
  apply (injective_iff_map_eq_zero (quotientPointHom q hq)).mpr
  intro u hu
  exact (quotientPoint_eq_zero q hq u.toMul).mp hu

omit [DecidableEq K] in
/-- Two unit arguments give the same Tate point exactly when their quotient classes agree. -/
theorem uniformizationPoint_eq_iff (q : Kˣ) (hq : valuation K (q : K) < 1) (u v : Kˣ) :
    uniformizationPoint q hq u = uniformizationPoint q hq v ↔
      (u : Kˣ ⧸ Subgroup.zpowers q) = v := by
  classical
  exact (quotientPointHom_injective q hq).eq_iff
    (a := Additive.ofMul (u : Kˣ ⧸ Subgroup.zpowers q))
    (b := Additive.ofMul (v : Kˣ ⧸ Subgroup.zpowers q))

end TateCurve
