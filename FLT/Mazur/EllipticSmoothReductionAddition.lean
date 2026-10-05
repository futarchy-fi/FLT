/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionAffineAddition
public import FLT.Mazur.EllipticReductionOpposite
public import FLT.Mazur.EllipticReductionTranslation

/-!
# Additive closure of smooth reduction

Combine the two integral slope charts, opposite smooth reductions and translation
by nonintegral points. The infinity fiber is closed without a lifting or
algebraic-closure assumption: an integral sum would contradict translation.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A) [DecidableEq (ResidueField A)]

omit [DecidableEq K] [DecidableEq (ResidueField A)] in
/-- A nonzero smooth reduction has integral affine coordinates upstairs. -/
theorem ReducesTo.integral {P : (W.map (algebraMap A K)).toAffine.Point}
    {p : (W.map (residue A)).toAffine.Point} (hp : ReducesTo A W P p) (hne : p ≠ 0) :
    ∃ x y : A, ∃ h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K),
      ∃ hr : (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y),
        P = .some _ _ h ∧ p = .some _ _ hr := by
  classical
  cases P with
  | zero => exact (hne (hp.unique A W (reducesTo_zero A W))).elim
  | some x y h =>
    have hx : x ∈ A := by
      by_contra hn
      exact hne (hp.unique A W (reducesTo_of_nonintegral A W h hn))
    have hy := W.mem_y_of_mem_x A h.1 hx
    have hs := (exists_reducesTo_iff A W (.some _ _ h)).mp ⟨p, hp⟩
    have hr := (smoothReduction_affine_iff A W ⟨x, hx⟩ ⟨y, hy⟩ h).mp hs
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, h, hr, rfl,
      hp.unique A W (reducesTo_integral A W _ _ h hr)⟩

omit [DecidableEq (ResidueField A)] in
/-- The sum of two points reducing to infinity again reduces to infinity. -/
theorem reducesTo_add_zero {P Q : (W.map (algebraMap A K)).toAffine.Point}
    (hp : ReducesTo A W P 0) (hq : ReducesTo A W Q 0) :
    ReducesTo A W (P + Q) 0 := by
  classical
  cases P with
  | zero => simpa only [← Affine.Point.zero_def, zero_add] using hq
  | some x y hP =>
    cases hs : Affine.Point.some x y hP + Q with
    | zero => exact reducesTo_zero A W
    | some u v hS =>
      apply reducesTo_of_nonintegral
      intro hu
      have hv := W.mem_y_of_mem_x A hS.1 hu
      let a : A := ⟨u, hu⟩
      let b : A := W.toAffine.negY a ⟨v, hv⟩
      have hb : (b : K) = (W.map (algebraMap A K)).toAffine.negY u v := rfl
      have hn : (W.map (algebraMap A K)).toAffine.Nonsingular (a : K) (b : K) :=
        (Affine.nonsingular_neg u v).mpr hS
      obtain ⟨r, s, h, he, _, _⟩ :=
        exists_integral_add_nonintegral A W a b hP hn (hp.not_mem_x A W)
      have hc : Affine.Point.some x y hP + Affine.Point.some (a : K) (b : K) hn = -Q := by
        have hn' : Affine.Point.some (a : K) (b : K) hn = -(.some u v hS) := rfl
        rw [hn', ← hs]
        abel
      have hi : ReducesTo A W (.some (r : K) (s : K) h) 0 := by
        rw [← he, hc]
        simpa only [neg_zero] using hq.neg A W
      exact hi.not_mem_x A W r.property

omit [DecidableEq (ResidueField A)] in
/-- Adding a point reducing to zero preserves any nonzero smooth reduction. -/
theorem reducesTo_add_zero_left {P Q : (W.map (algebraMap A K)).toAffine.Point}
    {q : (W.map (residue A)).toAffine.Point} (hp : ReducesTo A W P 0)
    (hq : ReducesTo A W Q q) (hne : q ≠ 0) : ReducesTo A W (P + Q) q := by
  obtain ⟨u, v, hQ, hr, rfl, rfl⟩ := hq.integral A W hne
  cases P with
  | zero => simpa only [← Affine.Point.zero_def, zero_add] using hq
  | some x y hP =>
    exact reducesTo_add_nonintegral_integral A W u v hP hQ hr (hp.not_mem_x A W)

/-- Actual smooth reduction is compatible with every sum, including both exceptional charts. -/
theorem ReducesTo.add {P Q : (W.map (algebraMap A K)).toAffine.Point}
    {p q : (W.map (residue A)).toAffine.Point}
    (hp : ReducesTo A W P p) (hq : ReducesTo A W Q q) :
    ReducesTo A W (P + Q) (p + q) := by
  by_cases hp0 : p = 0
  · subst p
    rw [zero_add]
    by_cases hq0 : q = 0
    · subst q
      exact reducesTo_add_zero A W hp hq
    · exact reducesTo_add_zero_left A W hp hq hq0
  by_cases hq0 : q = 0
  · subst q
    rw [add_zero, add_comm]
    exact reducesTo_add_zero_left A W hq hp hp0
  obtain ⟨x₁, y₁, h₁, hr₁, rfl, rfl⟩ := hp.integral A W hp0
  obtain ⟨x₂, y₂, h₂, hr₂, rfl, rfl⟩ := hq.integral A W hq0
  by_cases hred : residue A x₁ = residue A x₂ ∧ residue A y₁ =
      (W.map (residue A)).toAffine.negY (residue A x₂) (residue A y₂)
  · rw [Affine.Point.add_of_Y_eq hred.1 hred.2]
    exact reducesTo_add_of_residue_opposite A W x₁ y₁ x₂ y₂ h₁ h₂ hr₁ hred
  · exact reducesTo_add_of_residue_ne_neg A W x₁ y₁ x₂ y₂ h₁ h₂ hr₁ hr₂ hred

omit [DecidableEq K] [DecidableEq (ResidueField A)] in
/-- Smooth projective reduction is closed under addition. -/
theorem SmoothReduction.add {P Q : (W.map (algebraMap A K)).toProjective.Point}
    (hp : SmoothReduction A W P) (hq : SmoothReduction A W Q) :
    SmoothReduction A W (P + Q) := by
  classical
  let e := Point.toAffineAddEquiv (W.map (algebraMap A K)).toProjective
  have he (R) : (e R).toProjective = R := e.symm_apply_apply R
  obtain ⟨p, hrp⟩ := (exists_reducesTo_iff A W (e P)).mpr (by rwa [he])
  obtain ⟨q, hrq⟩ := (exists_reducesTo_iff A W (e Q)).mpr (by rwa [he])
  have hr := (exists_reducesTo_iff A W (e P + e Q)).mp ⟨p + q, hrp.add A W hrq⟩
  rwa [← map_add, he] at hr

omit [DecidableEq K] [DecidableEq (ResidueField A)] in
/-- Reduction on the smooth locus preserves addition as actual projective points. -/
theorem smoothReductionPoint_add
    (P Q : {P : (W.map (algebraMap A K)).toProjective.Point // SmoothReduction A W P}) :
    smoothReductionPoint A W ⟨P.val + Q.val, P.property.add A W Q.property⟩ =
      smoothReductionPoint A W P + smoothReductionPoint A W Q := by
  classical
  let e := Point.toAffineAddEquiv (W.map (algebraMap A K)).toProjective
  let er := Point.toAffineAddEquiv (W.map (residue A)).toProjective
  have he (R) : (e R).toProjective = R := e.symm_apply_apply R
  have her (R) : (er R).toProjective = R := er.symm_apply_apply R
  have hp : ReducesTo A W (e P.val) (er (smoothReductionPoint A W P)) := by
    unfold ReducesTo
    rw [he, her]
    rfl
  have hq : ReducesTo A W (e Q.val) (er (smoothReductionPoint A W Q)) := by
    unfold ReducesTo
    rw [he, her]
    rfl
  have hr := hp.add A W hq
  unfold ReducesTo at hr
  rw [← map_add, he, ← map_add, her] at hr
  exact Point.ext hr

end FLT.Mazur
