/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericAdditivity
public import FLT.FreyCurve.Serre.VeluSpecialization

/-!
# Specializing the Vélu addition identity

Function-field arithmetic specializes outside finitely many abscissae, uniformly
in the ordinate. This connects generic translations with the ordinary chord law.
-/

@[expose] public section

namespace WeierstrassCurve.Velu
open RatFunc
open scoped Polynomial
variable {K : Type*} [Field K] [CharZero K]
variable (E : WeierstrassCurve K)

/-- A function-field expression has the given values away from finitely many abscissae. -/
def EventuallyValue (z : FunctionField E) (f : K → K → K) : Prop :=
  ∀ᶠ x in Filter.cofinite, ∀ y, E.toAffine.Equation x y → affineValue E x y z = f x y

omit [CharZero K] in
/-- Constants specialize everywhere. -/
theorem EventuallyValue.constant (c : K) :
    EventuallyValue E (algebraMap K (FunctionField E) c) (fun _ _ => c) :=
  Filter.Eventually.of_forall fun x y _ => affineValue_constant E x y c

omit [CharZero K] in
/-- Eventual specialization respects addition. -/
theorem EventuallyValue.add {z w : FunctionField E} {f g : K → K → K}
    (hz : EventuallyValue E z f) (hw : EventuallyValue E w g) :
    EventuallyValue E (z + w) (fun x y => f x y + g x y) := by
  filter_upwards [hz, hw, eventually_regularAtAffine E z, eventually_regularAtAffine E w]
    with x hx hw hr hs y hy
  rw [affineValue_add E x y hr hs, hx y hy, hw y hy]

omit [CharZero K] in
/-- Eventual specialization respects multiplication. -/
theorem EventuallyValue.mul {z w : FunctionField E} {f g : K → K → K}
    (hz : EventuallyValue E z f) (hw : EventuallyValue E w g) :
    EventuallyValue E (z * w) (fun x y => f x y * g x y) := by
  filter_upwards [hz, hw, eventually_regularAtAffine E z, eventually_regularAtAffine E w]
    with x hx hw hr hs y hy
  rw [affineValue_mul E hy hr hs, hx y hy, hw y hy]

omit [CharZero K] in
/-- Eventual specialization respects negation. -/
theorem EventuallyValue.neg {z : FunctionField E} {f : K → K → K}
    (hz : EventuallyValue E z f) : EventuallyValue E (-z) (fun x y => -f x y) := by
  simpa using (EventuallyValue.constant E (-1)).mul E hz

omit [CharZero K] in
/-- Eventual specialization respects subtraction. -/
theorem EventuallyValue.sub {z w : FunctionField E} {f g : K → K → K}
    (hz : EventuallyValue E z f) (hw : EventuallyValue E w g) :
    EventuallyValue E (z - w) (fun x y => f x y - g x y) := by
  simpa only [sub_eq_add_neg] using hz.add E (hw.neg E)

/-- Eventual specialization respects inversion. -/
theorem EventuallyValue.inv {z : FunctionField E} {f : K → K → K}
    (hz : EventuallyValue E z f) : EventuallyValue E z⁻¹ (fun x y => (f x y)⁻¹) := by
  filter_upwards [hz, eventually_affineValue_inv E z] with x hx hi y hy
  rw [hi y hy, hx y hy]

/-- Eventual specialization respects division, including zero numerators or denominators. -/
theorem EventuallyValue.div {z w : FunctionField E} {f g : K → K → K}
    (hz : EventuallyValue E z f) (hw : EventuallyValue E w g) :
    EventuallyValue E (z / w) (fun x y => f x y / g x y) := by
  simpa only [div_eq_mul_inv] using hz.mul E (hw.inv E)

omit [CharZero K] in
/-- Eventual specialization respects natural powers. -/
theorem EventuallyValue.pow {z : FunctionField E} {f : K → K → K}
    (hz : EventuallyValue E z f) (n : ℕ) :
    EventuallyValue E (z ^ n) (fun x y => f x y ^ n) := by
  induction n with
  | zero => simpa using EventuallyValue.constant E 1
  | succ n hn => simpa only [pow_succ] using hn.mul E hz

omit [CharZero K] in
/-- The generic abscissa specializes to the ordinary abscissa. -/
theorem eventuallyValue_genericX : EventuallyValue E (genericX E) (fun x _ => x) := by
  exact Filter.Eventually.of_forall fun x y _ => by simp [genericX]

/-- The generic ordinate specializes to the ordinary ordinate. -/
theorem eventuallyValue_genericY : EventuallyValue E (genericY E) (fun _ y => y) := by
  apply Filter.Eventually.of_forall
  intro x y _
  rw [genericY, affineValue_liftY E E x y X 1 (RegularAt.X x)
    (by simpa using RegularAt.C x (1 : K))]
  simp only [eval_X, eval_one, one_mul]
  ring

omit [CharZero K] in
/-- Polynomial evaluation commutes with eventual specialization. -/
theorem EventuallyValue.aeval {z : FunctionField E} {f : K → K → K}
    (hz : EventuallyValue E z f) (p : K[X]) :
    EventuallyValue E (Polynomial.aeval z p) (fun x y => p.eval (f x y)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.eval_add] using hp.add E hq
  | monomial n c =>
    simpa only [Polynomial.aeval_monomial, Polynomial.eval_monomial] using
      (EventuallyValue.constant E c).mul E (hz.pow E n)

/-- Rational substitution commutes with specialization outside finitely many abscissae. -/
theorem EventuallyValue.substitution {z : FunctionField E} {f : K → K → K}
    (hz : EventuallyValue E z f) (ht : Transcendental K z) (r : K⟮X⟯) :
    EventuallyValue E (substitution z ht r)
      (fun x y => eval (RingHom.id K) (f x y) r) := by
  have h := (hz.aeval E r.num).div E (hz.aeval E r.denom)
  convert h using 1
  · conv_lhs => rw [← r.num_div_denom]
    simp only [map_div₀, map_polynomial_aeval, substitution_X]
  · simp only [RatFunc.eval, Polynomial.eval₂_id]

omit [CharZero K] in
/-- The chord abscissa commutes with eventual specialization. -/
theorem EventuallyValue.addX (E' : WeierstrassCurve K)
    {a b l : FunctionField E} {f g s : K → K → K}
    (ha : EventuallyValue E a f) (hb : EventuallyValue E b g)
    (hl : EventuallyValue E l s) :
    EventuallyValue E ((E'.map (algebraMap K _)).toAffine.addX a b l)
      (fun x y => E'.toAffine.addX (f x y) (g x y) (s x y)) := by
  exact (((hl.pow E 2).add E ((EventuallyValue.constant E E'.a₁).mul E hl)).sub E
    (EventuallyValue.constant E E'.a₂)).sub E ha |>.sub E hb

omit [CharZero K] in
/-- The chord ordinate commutes with eventual specialization. -/
theorem EventuallyValue.addY (E' : WeierstrassCurve K)
    {a b c l : FunctionField E} {f g h s : K → K → K}
    (ha : EventuallyValue E a f) (hb : EventuallyValue E b g)
    (hc : EventuallyValue E c h) (hl : EventuallyValue E l s) :
    EventuallyValue E ((E'.map (algebraMap K _)).toAffine.addY a b c l)
      (fun x y => E'.toAffine.addY (f x y) (g x y) (h x y) (s x y)) := by
  unfold Affine.addY Affine.negY Affine.negAddY
  exact (((hl.mul E ((ha.addX E E' hb hl).sub E ha)).add E hc).neg E |>.sub E
    ((EventuallyValue.constant E E'.a₁).mul E (ha.addX E E' hb hl))).sub E
    (EventuallyValue.constant E E'.a₃)

/-- Generic translation specializes to the ordinary chord coordinates. -/
theorem eventuallyValue_translate (u v : K) :
    EventuallyValue E (translateX E u v)
      (fun x y => E.toAffine.addX x u ((y - v) / (x - u))) ∧
    EventuallyValue E (translateY E u v)
      (fun x y => E.toAffine.addY x u y ((y - v) / (x - u))) := by
  have hx := eventuallyValue_genericX E
  have hy := eventuallyValue_genericY E
  have hu := EventuallyValue.constant E u
  have hv := EventuallyValue.constant E v
  have hs := (hy.sub E hv).div E (hx.sub E hu)
  exact ⟨hx.addX E E hu hs, hx.addY E E hu hy hs⟩

omit [CharZero K] in
/-- Every expression trivially specializes to its own affine value. -/
theorem EventuallyValue.self (z : FunctionField E) :
    EventuallyValue E z (fun x y => affineValue E x y z) :=
  Filter.Eventually.of_forall fun _ _ _ => rfl

/-- The substituted Vélu ordinate specializes by evaluating its two rational functions. -/
theorem eventuallyValue_imageY [DecidableEq K] (G : AddSubgroup E.toAffine.Point) [Fintype G]
    {z w : FunctionField E} {f g : K → K → K}
    (hz : EventuallyValue E z f) (hw : EventuallyValue E w g) (ht : Transcendental K z) :
    EventuallyValue E (imageY E G (substitution z ht) w)
      (fun x y =>
        (eval (RingHom.id K) (f x y) (slopeFunction E G) *
          (2 * g x y + E.a₁ * f x y + E.a₃) -
          E.a₁ * eval (RingHom.id K) (f x y) (xFunction E G) - E.a₃) / 2) := by
  have hs := hz.substitution E ht (slopeFunction E G)
  have hx := hz.substitution E ht (xFunction E G)
  have h := ((hs.mul E ((((EventuallyValue.constant E 2).mul E hw).add E
    ((EventuallyValue.constant E E.a₁).mul E hz)).add E
    (EventuallyValue.constant E E.a₃))).sub E
    ((EventuallyValue.constant E E.a₁).mul E hx)).sub E
    (EventuallyValue.constant E E.a₃) |>.div E (EventuallyValue.constant E 2)
  simpa only [imageY, imageX, substitution_X, map_ofNat] using h

/-- A nonconstant lifted abscissa eventually differs from a fixed constant. -/
theorem eventually_affineValue_liftX_ne (f : K⟮X⟯) (c : K) (hf : f - C c ≠ 0) :
    ∀ᶠ x in Filter.cofinite, ∀ y, E.toAffine.Equation x y →
      affineValue E x y (liftX E f) ≠ c := by
  have hz := sub_ne_zero.mpr (liftX_ne_constant E f c hf)
  have hs := (EventuallyValue.self E (liftX E f)).sub E (EventuallyValue.constant E c)
  filter_upwards [eventually_affineValue_ne_zero E hz, hs] with x hx hs y hy
  have hn := hx y hy
  rw [hs y hy] at hn
  exact sub_ne_zero.mp hn

variable [DecidableEq K] (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The rational Vélu coordinate formulas agree with the finite point sums. -/
theorem rational_values_eq_maps (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {x y : K}
    (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G) :
    eval (RingHom.id K) x (xFunction E G) = xMap E G (.some x y hP) ∧
    (eval (RingHom.id K) x (slopeFunction E G) * (2 * y + E.a₁ * x + E.a₃) -
        E.a₁ * eval (RingHom.id K) x (xFunction E G) - E.a₃) / 2 =
      yMap E G (.some x y hP) := by
  have h := affineValue_velu E G hodd hP hPG
  have hx := x_not_mem_kernelAbscissae E G hP hPG
  rw [affineValue_liftX] at h
  rw [affineValue_liftY E (curve E G) x y _ _
    (regular_eval_xFunction E G x hx).1 (regular_eval_slopeFunction E G x hx).1] at h
  exact h

/-- The generic addition identity is an equality of the two explicit chord coordinates. -/
theorem translated_image_coordinates [E.IsElliptic]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∉ G) :
    imageX E G (substitution _ (translateX_transcendental E hQ)) =
      liftTranslateX E (curve E G) (xFunction E G) (slopeFunction E G)
        (xMap E G (.some u v hQ)) (yMap E G (.some u v hQ)) ∧
    imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v) =
      liftTranslateY E (curve E G) (xFunction E G) (slopeFunction E G)
        (xMap E G (.some u v hQ)) (yMap E G (.some u v hQ)) := by
  classical
  obtain ⟨h, he⟩ := translated_image_eq_add E G hodd hQ hQG
  have hn := liftX_ne_constant E (xFunction E G) (xMap E G (.some u v hQ))
    (fun hz => xFunction_sub_C_not_degreeLE E G _ (Or.inl hz))
  rw [Affine.Point.add_of_X_ne hn] at he
  have hx := congrArg xCoord he
  have hy := congrArg yCoord he
  simpa only [xCoord, yCoord, Affine.slope_of_X_ne hn, liftTranslateX, liftTranslateY]
    using And.intro hx hy

omit [DecidableEq K] in
/-- Lifted target translation specializes to the target chord formula. -/
theorem eventuallyValue_liftTranslate (E' : WeierstrassCurve K) (f g : K⟮X⟯) (u v : K) :
    EventuallyValue E (liftTranslateX E E' f g u v)
      (fun x y => E'.toAffine.addX (affineValue E x y (liftX E f)) u
        ((affineValue E x y (liftY E E' f g) - v) /
          (affineValue E x y (liftX E f) - u))) ∧
    EventuallyValue E (liftTranslateY E E' f g u v)
      (fun x y => E'.toAffine.addY (affineValue E x y (liftX E f)) u
        (affineValue E x y (liftY E E' f g))
        ((affineValue E x y (liftY E E' f g) - v) /
          (affineValue E x y (liftX E f) - u))) := by
  have hx := EventuallyValue.self E (liftX E f)
  have hy := EventuallyValue.self E (liftY E E' f g)
  have hu := EventuallyValue.constant E u
  have hv := EventuallyValue.constant E v
  have hs := (hy.sub E hv).div E (hx.sub E hu)
  exact ⟨hx.addX E E' hu hs, hx.addY E E' hu hy hs⟩

/-- Outside finitely many abscissae, the Vélu point map respects translation
by a fixed affine point away from the kernel. -/
theorem eventually_pointMap_add_some [E.IsElliptic]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
    (h : ∀ P, P ∉ G → (curve E G).toAffine.Nonsingular (xMap E G P) (yMap E G P))
    {u v : K} (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∉ G) :
    ∀ᶠ x in Filter.cofinite, ∀ y (hP : E.toAffine.Nonsingular x y),
      Affine.Point.some x y hP ∉ G →
      Affine.Point.some x y hP + Affine.Point.some u v hQ ∉ G →
      pointMap E G (curve E G) h (.some x y hP + .some u v hQ) =
        pointMap E G (curve E G) h (.some x y hP) +
          pointMap E G (curve E G) h (.some u v hQ) := by
  have htr := eventuallyValue_translate E u v
  have hix := htr.1.substitution E (translateX_transcendental E hQ) (xFunction E G)
  have hiy := eventuallyValue_imageY E G htr.1 htr.2 (translateX_transcendental E hQ)
  have hrt := eventuallyValue_liftTranslate E (curve E G) (xFunction E G)
    (slopeFunction E G) (xMap E G (.some u v hQ)) (yMap E G (.some u v hQ))
  have heq := translated_image_coordinates E G hodd hQ hQG
  have hn := eventually_affineValue_liftX_ne E (xFunction E G)
    (xMap E G (.some u v hQ))
    (fun hz => xFunction_sub_C_not_degreeLE E G _ (Or.inl hz))
  filter_upwards [hix, hiy, hrt.1, hrt.2, hn,
    Filter.eventually_cofinite_ne u] with x hix hiy hrx hry hn hxu y hP hPG hSG
  have hpv := affineValue_velu E G hodd hP hPG
  have hne : xMap E G (.some x y hP) ≠ xMap E G (.some u v hQ) := by
    simpa only [hpv.1] using hn y hP.1
  have hs : E.toAffine.Nonsingular
      (E.toAffine.addX x u ((y - v) / (x - u)))
      (E.toAffine.addY x u y ((y - v) / (x - u))) := by
    simpa only [Affine.slope_of_X_ne hxu] using
      Affine.nonsingular_add hP hQ (fun hh => hxu hh.1)
  have hsum : Affine.Point.some x y hP + Affine.Point.some u v hQ =
      Affine.Point.some _ _ hs := by
    simp only [Affine.Point.add_of_X_ne hxu, Affine.slope_of_X_ne hxu]
  have hsv := rational_values_eq_maps E G hodd hs (by rwa [← hsum])
  have hx := congrArg (affineValue E x y) heq.1
  have hy := congrArg (affineValue E x y) heq.2
  change affineValue E x y (substitution _ (translateX_transcendental E hQ)
    (xFunction E G)) = _ at hx
  rw [hix y hP.1, hrx y hP.1, hsv.1, hpv.1, hpv.2] at hx
  rw [hiy y hP.1, hry y hP.1, hsv.2, hpv.1, hpv.2] at hy
  rw [← hsum] at hx hy
  simp only [pointMap, dite_eq_right hSG, dite_eq_right hPG, dite_eq_right hQG,
    Affine.Point.add_of_X_ne hne, Affine.slope_of_X_ne hne, Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

end WeierstrassCurve.Velu
