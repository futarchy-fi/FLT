/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.FiniteStages
public import FLT.TateCurve.LocalUniformization

/-!
# Tate uniformization over algebraic extensions

The local uniformizations glue over finite fields of definition. The resulting
quotient isomorphism commutes with every base-linear field homomorphism; in
particular it is equivariant for the Galois action on a separable closure.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine TateCurve.FiniteStages
namespace TateCurve.FiniteStages
variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [DecidableEq Ω]
  [Algebra.IsAlgebraic K Ω]
omit [Algebra.IsAlgebraic K Ω] in
/-- Equality of finite-stage points is exactly equality of the ambient quotient classes. -/
theorem point_eq_iff (L : IntermediateField K Ω) [FiniteDimensional K L]
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u v : Lˣ) :
    point L q hq u = point L q hq v ↔
      (Units.map L.val.toRingHom.toMonoidHom u :
        Ωˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K Ω).toMonoidHom q)) =
      Units.map L.val.toRingHom.toMonoidHom v := by
  classical
  rw [point, point, (WeierstrassCurve.Affine.Point.map_injective L.val).eq_iff,
    uniformizationPointOver_eq_iff, QuotientGroup.eq_iff_div_mem,
    QuotientGroup.eq_iff_div_mem, ← map_div]
  have hqmap : Units.map L.val.toRingHom.toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom q) =
      Units.map (algebraMap K Ω).toMonoidHom q := rfl
  rw [← hqmap]
  exact (map_mem_zpowers_iff _ (Units.map_injective L.val.injective) _ _).symm

/-- The glued map has exactly the fibers prescribed by the Tate parameter. -/
theorem algebraicPoint_eq_iff (q : Kˣ) (hq : valuation K (q : K) < 1) (u v : Ωˣ) :
    algebraicPoint q hq u = algebraicPoint q hq v ↔
      (u : Ωˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K Ω).toMonoidHom q)) = v := by
  classical
  obtain ⟨L, hL, a, ha⟩ := exists_finite_unit (K := K) u
  obtain ⟨M, hM, b, hb⟩ := exists_finite_unit (K := K) v
  let := hL
  let := hM
  let f := IntermediateField.inclusion (show L ≤ L ⊔ M from le_sup_left)
  let g := IntermediateField.inclusion (show M ≤ L ⊔ M from le_sup_right)
  let a' := Units.map f.toRingHom.toMonoidHom a
  let b' := Units.map g.toRingHom.toMonoidHom b
  have ha' : Units.map (L ⊔ M).val.toRingHom.toMonoidHom a' = u := ha
  have hb' : Units.map (L ⊔ M).val.toRingHom.toMonoidHom b' = v := hb
  rw [← ha', ← hb', algebraicPoint_map, algebraicPoint_map, point_eq_iff]

/-- Every point over an algebraic extension has a Tate parameter. -/
theorem algebraicPoint_surjective (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Function.Surjective (algebraicPoint (Ω := Ω) q hq) := by
  classical
  intro P
  obtain ⟨L, hL, Q, hQ⟩ := exists_finite_point (WeierstrassCurve.tateCurve (q : K)) P
  let := hL
  let e := WeierstrassCurve.Affine.Point.equivOfEq
    (WeierstrassCurve.tateCurve_baseChange (l := L) (q : K) hq).symm
  obtain ⟨u, hu⟩ := uniformizationPoint_surjective
    (Units.map (algebraMap K L).toMonoidHom q) (valuation_algebraMap_lt_one (l := L) hq) (e.symm Q)
  refine ⟨Units.map L.val.toRingHom.toMonoidHom u, ?_⟩
  rw [algebraicPoint_map]
  change WeierstrassCurve.Affine.Point.map L.val
    (e (uniformizationPoint (Units.map (algebraMap K L).toMonoidHom q)
      (valuation_algebraMap_lt_one (l := L) hq) u)) = P
  rw [hu, e.apply_symm_apply, hQ]

/-- The glued map descends to the multiplicative quotient. -/
noncomputable def algebraicQuotientPoint (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Ωˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K Ω).toMonoidHom q) →
      ((WeierstrassCurve.tateCurve (q : K))⁄Ω).Point :=
  Quotient.lift (algebraicPoint q hq) (fun _ _ h ↦
    (algebraicPoint_eq_iff q hq _ _).mpr (Quotient.sound h))

/-- The algebraic Tate quotient map is additive. -/
noncomputable def algebraicQuotientHom (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Additive (Ωˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K Ω).toMonoidHom q)) →+
      ((WeierstrassCurve.tateCurve (q : K))⁄Ω).Point :=
  AddMonoidHom.mk' (fun u ↦ algebraicQuotientPoint q hq u.toMul) (by
    intro a b
    change algebraicQuotientPoint q hq (a.toMul * b.toMul) =
      algebraicQuotientPoint q hq a.toMul + algebraicQuotientPoint q hq b.toMul
    induction a.toMul using Quotient.inductionOn with
    | h u =>
      induction b.toMul using Quotient.inductionOn with
      | h v => exact algebraicPoint_mul q hq u v)

/-- Tate uniformization over every algebraic extension of a local field. -/
noncomputable def algebraicUniformization (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Additive (Ωˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K Ω).toMonoidHom q)) ≃+
      ((WeierstrassCurve.tateCurve (q : K))⁄Ω).Point :=
  AddEquiv.ofBijective (algebraicQuotientHom q hq) ⟨by
    intro a b
    change algebraicQuotientPoint q hq a.toMul = algebraicQuotientPoint q hq b.toMul →
      a.toMul = b.toMul
    induction a.toMul using Quotient.inductionOn with
    | h u =>
      induction b.toMul using Quotient.inductionOn with
      | h v => exact (algebraicPoint_eq_iff q hq u v).mp, by
    intro P
    obtain ⟨u, hu⟩ := algebraicPoint_surjective q hq P
    exact ⟨Additive.ofMul u, hu⟩⟩

variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [Algebra.IsAlgebraic K Ω'] [DecidableEq Ω']
/-- Algebra homomorphisms commute with the glued Tate point map. -/
theorem map_algebraicPoint (f : Ω →ₐ[K] Ω') (q : Kˣ)
    (hq : valuation K (q : K) < 1) (u : Ωˣ) :
    WeierstrassCurve.Affine.Point.map f (algebraicPoint q hq u) =
      algebraicPoint q hq (Units.map f.toRingHom.toMonoidHom u) := by
  classical
  obtain ⟨L, hL, a, ha⟩ := exists_finite_unit (K := K) u
  let := hL
  let M := L.map f
  let g := (L.equivMap f).toAlgHom
  have : FiniteDimensional K M := LinearEquiv.finiteDimensional (L.equivMap f).toLinearEquiv
  have hcomp : M.val.comp g = f.comp L.val := rfl
  rw [← ha, algebraicPoint_map]
  have hunit : Units.map f.toRingHom.toMonoidHom (Units.map L.val.toRingHom.toMonoidHom a) =
      Units.map M.val.toRingHom.toMonoidHom (Units.map g.toRingHom.toMonoidHom a) := rfl
  rw [hunit, algebraicPoint_map]
  unfold point
  rw [← map_uniformizationPointOver g
    (continuous_algHom_of_finite g (continuous_algebraMap L) (continuous_algebraMap M)),
    WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map, hcomp]

end TateCurve.FiniteStages
