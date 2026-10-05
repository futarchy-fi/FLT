/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeUniformizerLabel
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# Primitive nodal coordinates under small integral variable changes

A unit scaling, a shear in the maximal ideal, and translations deeper than
the common coordinate depth preserve primitive coordinates and their signed
branch label. The witness represents the actual generic variable-change map.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} [(W.map (algebraMap A K)).IsElliptic]
  (C : VariableChange A)

/-- The actual projective variable change has the usual affine coordinates. -/
theorem integralProjectiveVariableChange_affine (x y : K)
    (h : ((C • W).map (algebraMap A K)).toAffine.Nonsingular x y)
    (hs : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((C.u : K) ^ 2 * x + C.r) ((C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t)) :
    integralProjectiveVariableChange A W C (Affine.Point.toProjective (.some x y h)) =
      Affine.Point.toProjective (.some _ _ hs) := by
  change (((Projective.Point.toAffineAddEquiv _).trans
    (integralAffineVariableChange A W C)).trans
    (Projective.Point.toAffineAddEquiv _).symm)
    ((Projective.Point.toAffineAddEquiv _).symm (.some x y h)) = _
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  simp only [integralAffineVariableChange, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
    Affine.Point.equivVariableChange_some, Projective.Point.toAffineAddEquiv_symm_apply]
  rfl

/-- Deep translations under any integral change preserve primitive coordinate depth. -/
theorem exists_nodePointCoordinates_integralChange {π : A}
    {P : ((C • W).map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A (C • W) π P)
    {ρ τ : A}
    (hρ : ρ ∈ maximalIdeal A) (hτ : τ ∈ maximalIdeal A)
    (hr : C.r = π ^ v.depth * ρ) (ht : C.t = π ^ v.depth * τ) :
    ∃ w : NodePointCoordinates A W π (integralProjectiveVariableChange A W C P),
      w.depth = v.depth ∧ w.a = (C.u : A) ^ 2 * v.a + ρ ∧
        w.b = (C.u : A) ^ 3 * v.b + (C.u : A) ^ 2 * C.s * v.a + τ := by
  let a : A := (C.u : A) ^ 2 * v.a + ρ
  let b : A := (C.u : A) ^ 3 * v.b + (C.u : A) ^ 2 * C.s * v.a + τ
  have hx : π ^ v.depth * a = (C.u : A) ^ 2 * (π ^ v.depth * v.a) + C.r := by
    rw [hr]
    dsimp only [a]
    ring
  have hy : π ^ v.depth * b = (C.u : A) ^ 3 * (π ^ v.depth * v.b) +
      (C.u : A) ^ 2 * C.s * (π ^ v.depth * v.a) + C.t := by
    rw [ht]
    dsimp only [b]
    ring
  have he : ((C.map (algebraMap A K)) • (W.map (algebraMap A K))).toAffine.Equation
      ((π ^ v.depth * v.a : A) : K) ((π ^ v.depth * v.b : A) : K) := by
    rw [map_variableChange]
    exact v.nonsingular.1
  have hns0 := Affine.equation_iff_nonsingular.mp
    ((Affine.variableChange_equation (W.map (algebraMap A K)) (C.map (algebraMap A K))
      _ _).mpr he)
  have hns : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((π ^ v.depth * a : A) : K) ((π ^ v.depth * b : A) : K) := by
    simpa [hx, hy, VariableChange.map] using hns0
  have ha : residue A a = residue A (C.u : A) ^ 2 * residue A v.a := by
    simp [a, (residue_eq_zero_iff _).mpr hρ]
  have hu : residue A (C.u : A) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr C.u.isUnit
  have hp : IsUnit a ∨ IsUnit b := by
    by_cases hva : IsUnit v.a
    · exact Or.inl ((residue_ne_zero_iff_isUnit _).mp
        (ha ▸ mul_ne_zero (pow_ne_zero 2 hu) ((residue_ne_zero_iff_isUnit _).mpr hva)))
    · right
      apply (residue_ne_zero_iff_isUnit _).mp
      simpa [b, (residue_eq_zero_iff _).mpr hva, (residue_eq_zero_iff _).mpr hτ] using
        mul_ne_zero (pow_ne_zero 3 hu)
          ((residue_ne_zero_iff_isUnit _).mpr (v.primitive.resolve_left hva))
  refine ⟨⟨v.depth, a, b, hp, hns, ?_⟩, rfl, rfl, rfl⟩
  · conv_lhs => rw [v.represents]
    have hh := integralProjectiveVariableChange_affine C _ _ v.nonsingular hns0
    apply hh.trans
    apply congrArg Affine.Point.toProjective
    apply Affine.Point.some_eq_some
    · exact (congrArg (fun z : A => (z : K)) hx).symm
    · exact (congrArg (fun z : A => (z : K)) hy).symm

/-- Deep translations and a small shear preserve primitive witnesses and branch labels. -/
theorem exists_nodePointCoordinates_smallChange {π : A} {n : ℕ}
    {P : ((C • W).map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A (C • W) π P)
    (hs : C.s ∈ maximalIdeal A) {ρ τ : A}
    (hρ : ρ ∈ maximalIdeal A) (hτ : τ ∈ maximalIdeal A)
    (hr : C.r = π ^ v.depth * ρ) (ht : C.t = π ^ v.depth * τ) :
    ∃ w : NodePointCoordinates A W π (integralProjectiveVariableChange A W C P),
      w.depth = v.depth ∧ nodeBranchLabel n w.depth w.b = nodeBranchLabel n v.depth v.b := by
  obtain ⟨w, hk, _, hb⟩ := exists_nodePointCoordinates_integralChange C v hρ hτ hr ht
  have he : residue A w.b = residue A (C.u : A) ^ 3 * residue A v.b := by
    simp [hb, (residue_eq_zero_iff _).mpr hs, (residue_eq_zero_iff _).mpr hτ]
  have hu : residue A (C.u : A) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr C.u.isUnit
  have hm : w.b ∈ maximalIdeal A ↔ v.b ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, ← residue_eq_zero_iff, he, mul_eq_zero]
    simp [pow_ne_zero 3 hu]
  refine ⟨w, hk, ?_⟩
  unfold nodeBranchLabel
  rw [hk]
  congr 1
  exact propext (or_congr Iff.rfl hm)

end FLT.Mazur
