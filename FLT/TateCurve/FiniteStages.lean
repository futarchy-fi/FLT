/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.FiniteExtension
public import FLT.TateCurve.Naturality
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite fields of definition for Tate points

Compatible local-field structures make the coordinate construction independent
of the finite intermediate field containing a given algebraic parameter.
-/

@[expose] public section

open ValuativeRel
namespace TateCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [TopologicalSpace L] [IsTopologicalDivisionRing L]
  [T2Space L] [Algebra K L] [FiniteDimensional K L]
variable {M : Type*} [Field M] [TopologicalSpace M] [IsTopologicalDivisionRing M] [Algebra K M]
/-- Morphisms between compatible finite local extensions are automatically continuous. -/
theorem continuous_algHom_of_finite (f : L →ₐ[K] M)
    (hL : Continuous (algebraMap K L)) (hM : Continuous (algebraMap K M)) : Continuous f := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  have : ContinuousSMul K L := continuousSMul_of_algebraMap K L hL
  have : ContinuousSMul K M := continuousSMul_of_algebraMap K M hM
  exact f.toLinearMap.continuous_of_finiteDimensional
end TateCurve

open scoped WeierstrassCurve.Affine
namespace TateCurve
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
/-- Every unit of an algebraic extension comes from a finite intermediate field. -/
theorem exists_finite_unit (u : Ωˣ) :
    ∃ L : IntermediateField K Ω, ∃ _ : FiniteDimensional K L,
      ∃ v : Lˣ, Units.map L.val.toRingHom.toMonoidHom v = u := by
  let L := IntermediateField.adjoin K {(u : Ω)}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (u : Ω)).isIntegral
  let a : L := ⟨u, IntermediateField.mem_adjoin_simple_self K (u : Ω)⟩
  have ha : a ≠ 0 := fun h ↦ u.ne_zero (congrArg Subtype.val h)
  exact ⟨L, inferInstance, Units.mk0 a ha, Units.ext rfl⟩

variable [DecidableEq Ω]
/-- Every elliptic-curve point of an algebraic extension comes from a finite intermediate field. -/
theorem exists_finite_point (E : WeierstrassCurve K) (P : (E⁄Ω).Point) :
    ∃ L : IntermediateField K Ω, ∃ _ : FiniteDimensional K L,
      ∃ Q : (E⁄L).Point, WeierstrassCurve.Affine.Point.map L.val Q = P := by
  classical
  cases P with
  | zero =>
    exact ⟨⊥, inferInstance, 0, rfl⟩
  | some x y h =>
    let L := IntermediateField.adjoin K {x, y}
    have : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin_pair
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    let a : L := ⟨x, IntermediateField.mem_adjoin_pair_left K x y⟩
    let b : L := ⟨y, IntermediateField.mem_adjoin_pair_right K x y⟩
    have hab : (E⁄L).Nonsingular a b := (E.toAffine.baseChange_nonsingular L.val.injective a b).mp h
    exact ⟨L, inferInstance, .some a b hab, rfl⟩
end TateCurve

open ValuativeRel
open scoped WeierstrassCurve.Affine
namespace TateCurve
namespace FiniteStages
variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]
/-- A chosen compatible valuative relation on a finite intermediate field. -/
noncomputable scoped instance valuativeRel (L : IntermediateField K Ω) [FiniteDimensional K L] :
    ValuativeRel L := (exists_localField_extension K L).choose
/-- A chosen compatible topology on a finite intermediate field. -/
noncomputable scoped instance topologicalSpace (L : IntermediateField K Ω) [FiniteDimensional K L] :
    TopologicalSpace L := (exists_localField_extension K L).choose_spec.choose
open scoped FiniteStages
/-- Each chosen finite intermediate field is a local field. -/
scoped instance isLocal (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsNonarchimedeanLocalField L :=
  (exists_localField_extension K L).choose_spec.choose_spec.1
/-- The base field embeds valuatively into each chosen intermediate field. -/
scoped instance isExtension (L : IntermediateField K Ω) [FiniteDimensional K L] :
    ValuativeExtension K L :=
  (exists_localField_extension K L).choose_spec.choose_spec.2.1
/-- The inclusion of the base into a chosen intermediate field is continuous. -/
theorem continuous_algebraMap (L : IntermediateField K Ω) [FiniteDimensional K L] :
    Continuous (algebraMap K L) :=
  (exists_localField_extension K L).choose_spec.choose_spec.2.2.1

variable [DecidableEq Ω]
/-- A Tate point computed in a finite intermediate field and mapped to the ambient field. -/
noncomputable def point (L : IntermediateField K Ω) [FiniteDimensional K L]
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ) :
    ((WeierstrassCurve.tateCurve (q : K))⁄Ω).Point := by
  classical
  exact WeierstrassCurve.Affine.Point.map L.val (uniformizationPointOver L q hq u)
/-- Each finite-stage Tate point map respects multiplication. -/
theorem point_mul (L : IntermediateField K Ω) [FiniteDimensional K L]
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u v : Lˣ) :
    point L q hq (u * v) = point L q hq u + point L q hq v := by
  classical
  unfold point
  rw [uniformizationPointOver_mul, map_add]

/-- Computing in a larger finite intermediate field gives the same ambient Tate point. -/
theorem point_map {L M : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K M] (f : L →ₐ[K] M) (hf : M.val.comp f = L.val)
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ) :
    point M q hq (Units.map f.toRingHom.toMonoidHom u) = point L q hq u := by
  classical
  unfold point
  rw [← map_uniformizationPointOver f
    (continuous_algHom_of_finite f (continuous_algebraMap L) (continuous_algebraMap M)),
    WeierstrassCurve.Affine.Point.map_map, hf]

/-- The ambient Tate point depends only on the unit, independently of its field of definition. -/
theorem point_eq_of_map_eq {L M : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K M] (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ) (v : Mˣ)
    (h : Units.map L.val.toRingHom.toMonoidHom u = Units.map M.val.toRingHom.toMonoidHom v) :
    point L q hq u = point M q hq v := by
  classical
  let f := IntermediateField.inclusion (show L ≤ L ⊔ M from le_sup_left)
  let g := IntermediateField.inclusion (show M ≤ L ⊔ M from le_sup_right)
  have huv : Units.map f.toRingHom.toMonoidHom u = Units.map g.toRingHom.toMonoidHom v := by
    apply Units.ext
    apply Subtype.val_injective
    exact congrArg Units.val h
  rw [← point_map f rfl q hq u, ← point_map g rfl q hq v, huv]

variable [Algebra.IsAlgebraic K Ω]
/-- The Tate point over an algebraic extension, computed in a finite field of definition. -/
noncomputable def algebraicPoint (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Ωˣ) :
    ((WeierstrassCurve.tateCurve (q : K))⁄Ω).Point := by
  classical
  let L := (exists_finite_unit (K := K) u).choose
  let := (exists_finite_unit (K := K) u).choose_spec.choose
  let v := (exists_finite_unit (K := K) u).choose_spec.choose_spec.choose
  exact point L q hq v

/-- The glued point map agrees with every finite-stage construction. -/
theorem algebraicPoint_map (L : IntermediateField K Ω) [FiniteDimensional K L]
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ) :
    algebraicPoint q hq (Units.map L.val.toRingHom.toMonoidHom u) = point L q hq u := by
  classical
  unfold algebraicPoint
  let := (exists_finite_unit (K := K) (Units.map L.val.toRingHom.toMonoidHom u)).choose_spec.choose
  apply point_eq_of_map_eq
  have h := exists_finite_unit (K := K) (Units.map L.val.toRingHom.toMonoidHom u)
  exact h.choose_spec.choose_spec.choose_spec

/-- The glued Tate point map respects multiplication of ambient units. -/
theorem algebraicPoint_mul (q : Kˣ) (hq : valuation K (q : K) < 1) (u v : Ωˣ) :
    algebraicPoint q hq (u * v) = algebraicPoint q hq u + algebraicPoint q hq v := by
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
  rw [← ha', ← hb', ← map_mul, algebraicPoint_map, algebraicPoint_map,
    algebraicPoint_map, point_mul]

end FiniteStages
end TateCurve
