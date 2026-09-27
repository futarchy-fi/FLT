/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluEquation

/-!
# Partial fractions and the differential equation for Vélu sums

Pairwise partial fractions express the differential residual of a finite pole sum
in terms of two regular sums at each pole. Translation and duplication identify
these sums for a finite kernel with no nonzero points fixed by negation.

The final theorem proves the second-order differential identity away from the
kernel abscissae. Recovering the candidate curve equation requires a further
constant-of-integration argument; nonsingularity and additivity are not proved here.
-/

@[expose] public section

open scoped BigOperators
namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K]

/-- A double-pole contribution to the rational x-coordinate. -/
def polePart (a c u x : K) : K := c / (x - u) + a / (x - u) ^ 2
/-- The formal first derivative of a double-pole contribution. -/
def poleSlope (a c u x : K) : K := -c / (x - u) ^ 2 - 2 * a / (x - u) ^ 3
/-- The formal second derivative of a double-pole contribution. -/
def poleCurvature (a c u x : K) : K := 2 * c / (x - u) ^ 3 + 6 * a / (x - u) ^ 4

/-- Partial fractions for the product of contributions at two distinct poles. -/
theorem polePart_mul (a c u a' c' v x : K) (huv : u ≠ v) (hxu : x ≠ u)
    (hxv : x ≠ v) :
    polePart a c u x * polePart a' c' v x =
      a * polePart a' c' v u / (x - u) ^ 2 +
        (c * polePart a' c' v u + a * poleSlope a' c' v u) / (x - u) +
      a' * polePart a c u v / (x - v) ^ 2 +
        (c' * polePart a c u v + a' * poleSlope a c u v) / (x - v) := by
  dsimp [polePart, poleSlope]
  field_simp
  ring

/-- The differential residual of one pole contribution. -/
theorem polePart_differential (a c b u x : K) (hx : x ≠ u) :
    2 * (a + 2 * c * (x - u) + (12 * u + b) * (x - u) ^ 2 + 4 * (x - u) ^ 3) *
        poleCurvature a c u x +
      (2 * c + 2 * (12 * u + b) * (x - u) + 12 * (x - u) ^ 2) *
        poleSlope a c u x -
      (24 * x + 2 * b) * polePart a c u x - 12 * polePart a c u x ^ 2 =
      -20 * c + (6 * a * b + 72 * a * u - 6 * c ^ 2) / (x - u) ^ 2 := by
  dsimp [polePart, poleSlope, poleCurvature]
  field_simp
  ring

/-- Swapping the indices of a finite sum off the diagonal preserves the sum. -/
theorem sum_erase_swap {ι A : Type*} [DecidableEq ι] [AddCommGroup A]
    (S : Finset ι) (f : ι → ι → A) :
    (∑ i ∈ S, ∑ j ∈ S.erase i, f i j) =
      ∑ i ∈ S, ∑ j ∈ S.erase i, f j i := by
  have h (f : ι → ι → A) :
      (∑ i ∈ S, ∑ j ∈ S.erase i, f i j) =
        (∑ i ∈ S, ∑ j ∈ S, f i j) - ∑ i ∈ S, f i i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact eq_sub_of_add_eq (Finset.sum_erase_add S (f i) hi)
  rw [h f, h (fun i j => f j i)]
  rw [Finset.sum_comm]

/-- Partial fractions for the square of a finite pole sum. -/
theorem sum_polePart_sq [DecidableEq K] (S : Finset K) (a c : K → K) (x : K)
    (hx : ∀ u ∈ S, x ≠ u) :
    (∑ u ∈ S, polePart (a u) (c u) u x) ^ 2 =
      (∑ u ∈ S, polePart (a u) (c u) u x ^ 2) +
        2 * ∑ u ∈ S,
          (a u * (∑ v ∈ S.erase u, polePart (a v) (c v) v u) / (x - u) ^ 2 +
            (c u * (∑ v ∈ S.erase u, polePart (a v) (c v) v u) +
              a u * (∑ v ∈ S.erase u, poleSlope (a v) (c v) v u)) / (x - u)) := by
  let p (u v : K) := a u * polePart (a v) (c v) v u / (x - u) ^ 2 +
    (c u * polePart (a v) (c v) v u + a u * poleSlope (a v) (c v) v u) / (x - u)
  have hsplit :
      (∑ u ∈ S, polePart (a u) (c u) u x) ^ 2 =
        (∑ u ∈ S, polePart (a u) (c u) u x ^ 2) +
          ∑ u ∈ S, ∑ v ∈ S.erase u,
            polePart (a u) (c u) u x * polePart (a v) (c v) v x := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [pow_two, add_comm]
    exact (Finset.sum_erase_add S
      (fun v => polePart (a u) (c u) u x * polePart (a v) (c v) v x) hu).symm
  have hp : (∑ u ∈ S, ∑ v ∈ S.erase u,
      polePart (a u) (c u) u x * polePart (a v) (c v) v x) =
        2 * ∑ u ∈ S, ∑ v ∈ S.erase u, p u v := by
    calc
      _ = ∑ u ∈ S, ∑ v ∈ S.erase u, (p u v + p v u) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [p, add_assoc] using
          polePart_mul (a u) (c u) u (a v) (c v) v x (Finset.ne_of_mem_erase hv).symm
            (hx u hu) (hx v (Finset.mem_of_mem_erase hv))
      _ = (∑ u ∈ S, ∑ v ∈ S.erase u, p u v) +
          ∑ u ∈ S, ∑ v ∈ S.erase u, p v u := by
        simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ u ∈ S, ∑ v ∈ S.erase u, p u v := by
        rw [← sum_erase_swap S p]
        ring
  rw [hsplit, hp]
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  simp only [p, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]

/-- The differential residual of a finite pole sum, expressed using regular sums. -/
theorem sum_polePart_differential [DecidableEq K] (S : Finset K) (b e d x : K)
    (hx : ∀ u ∈ S, x ≠ u) :
    let a := fun u : K => 4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d
    let c := fun u : K => 6 * u ^ 2 + b * u + e
    let X := x + ∑ u ∈ S, polePart (a u) (c u) u x
    let D := 1 + ∑ u ∈ S, poleSlope (a u) (c u) u x
    let DD := ∑ u ∈ S, poleCurvature (a u) (c u) u x
    2 * a x * DD + 2 * c x * D - 12 * X ^ 2 - 2 * b * X - 2 * e +
        20 * (∑ u ∈ S, c u) =
      ∑ u ∈ S,
        ((6 * a u * b + 72 * a u * u - 6 * c u ^ 2) / (x - u) ^ 2 -
          24 * (a u * (∑ v ∈ S.erase u, polePart (a v) (c v) v u) / (x - u) ^ 2 +
            (c u * (∑ v ∈ S.erase u, polePart (a v) (c v) v u) +
              a u * (∑ v ∈ S.erase u, poleSlope (a v) (c v) v u)) / (x - u))) := by
  let a := fun u : K => 4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d
  let c := fun u : K => 6 * u ^ 2 + b * u + e
  have hsingle (u : K) (hu : u ∈ S) :
      2 * a x * poleCurvature (a u) (c u) u x +
        2 * c x * poleSlope (a u) (c u) u x -
        (24 * x + 2 * b) * polePart (a u) (c u) u x -
        12 * polePart (a u) (c u) u x ^ 2 =
      -20 * c u + (6 * a u * b + 72 * a u * u - 6 * c u ^ 2) / (x - u) ^ 2 := by
    have ha : a x = a u + 2 * c u * (x - u) +
        (12 * u + b) * (x - u) ^ 2 + 4 * (x - u) ^ 3 := by dsimp [a, c]; ring
    have hc : 2 * c x = 2 * c u + 2 * (12 * u + b) * (x - u) +
        12 * (x - u) ^ 2 := by dsimp [c]; ring
    rw [ha, hc]
    exact polePart_differential (a u) (c u) b u x (hx u hu)
  have hsum := Finset.sum_congr rfl hsingle
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hsq := sum_polePart_sq S a c x hx
  dsimp only
  change 2 * a x * _ + 2 * c x * _ - 12 * _ ^ 2 - 2 * b * _ - 2 * e +
    20 * (∑ u ∈ S, c u) = _
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hc : 2 * c x = 12 * x ^ 2 + 2 * b * x + 2 * e := by dsimp [c]; ring
  linear_combination hsum - 12 * hsq + hc

/-- Two local regular-sum identities annihilate the differential residual. -/
theorem sum_polePart_differential_eq_zero [DecidableEq K] (S : Finset K)
    (b e d x : K) (hx : ∀ u ∈ S, x ≠ u)
    (h₀ : ∀ u ∈ S,
      let a := fun v : K => 4 * v ^ 3 + b * v ^ 2 + 2 * e * v + d
      let c := fun v : K => 6 * v ^ 2 + b * v + e
      a u * (b + 12 * u) - c u ^ 2 =
        4 * a u * ∑ v ∈ S.erase u, polePart (a v) (c v) v u)
    (h₁ : ∀ u ∈ S,
      let a := fun v : K => 4 * v ^ 3 + b * v ^ 2 + 2 * e * v + d
      let c := fun v : K => 6 * v ^ 2 + b * v + e
      c u * (∑ v ∈ S.erase u, polePart (a v) (c v) v u) +
        a u * (∑ v ∈ S.erase u, poleSlope (a v) (c v) v u) = 0) :
    let a := fun u : K => 4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d
    let c := fun u : K => 6 * u ^ 2 + b * u + e
    let X := x + ∑ u ∈ S, polePart (a u) (c u) u x
    let D := 1 + ∑ u ∈ S, poleSlope (a u) (c u) u x
    let DD := ∑ u ∈ S, poleCurvature (a u) (c u) u x
    2 * a x * DD + 2 * c x * D - 12 * X ^ 2 - 2 * b * X - 2 * e +
        20 * (∑ u ∈ S, c u) = 0 := by
  dsimp only
  rw [sum_polePart_differential S b e d x hx]
  apply Finset.sum_eq_zero
  intro u hu
  have h := h₀ u hu
  dsimp only at h
  have hn :
      6 * (4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d) * b +
        72 * (4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d) * u -
        6 * (6 * u ^ 2 + b * u + e) ^ 2 =
      24 * ((4 * u ^ 3 + b * u ^ 2 + 2 * e * u + d) *
        ∑ v ∈ S.erase u, polePart
          (4 * v ^ 3 + b * v ^ 2 + 2 * e * v + d) (6 * v ^ 2 + b * v + e) v u) := by
    linear_combination 6 * h
  rw [hn, h₁ u hu]
  simp only [zero_div, add_zero]
  ring

open scoped WeierstrassCurve.Affine

/-- Negation preserves the affine x-coordinate, including the chosen value at zero. -/
theorem xCoord_neg (E : WeierstrassCurve K) (P : E.toAffine.Point) :
    xCoord (-P) = xCoord P := by
  cases P <;> rfl

/-- Two nonzero points have the same x-coordinate exactly when they differ by sign. -/
theorem xCoord_eq_iff (E : WeierstrassCurve K)
    {P Q : E.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    xCoord P = xCoord Q ↔ P = Q ∨ P = -Q := by
  classical
  constructor
  · intro h
    apply Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep
    cases P with
    | zero => exact (hP rfl).elim
    | some x y hp =>
      cases Q with
      | zero => exact (hQ rfl).elim
      | some u v hq =>
        simp only [xCoord] at h
        simp only [Affine.Point.xRep_some, h]
  · rintro (rfl | rfl)
    · rfl
    · exact xCoord_neg E Q

/-- Each distinct x-coordinate contributes twice when every inverse pair has two elements. -/
theorem sum_xCoord_image [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) (S : Finset G)
    (hzero : (0 : G) ∉ S) (hneg : ∀ Q ∈ S, -Q ∈ S)
    (hpair : ∀ Q ∈ S, Q ≠ -Q) (f : K → K) :
    (∑ Q ∈ S, f (xCoord Q.val)) =
      2 * ∑ u ∈ S.image (fun Q => xCoord Q.val), f u := by
  have hfiber (Q : G) (hQ : Q ∈ S) :
      S.filter (fun R => xCoord R.val = xCoord Q.val) = {Q, -Q} := by
    ext R
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hR, hx⟩
      have hR0 : R.val ≠ 0 := by
        intro hz
        exact hzero ((Subtype.ext hz : R = 0) ▸ hR)
      have hQ0 : Q.val ≠ 0 := by
        intro hz
        exact hzero ((Subtype.ext hz : Q = 0) ▸ hQ)
      rcases (xCoord_eq_iff E hR0 hQ0).mp hx with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact ⟨hQ, rfl⟩
      · exact ⟨hneg Q hQ, xCoord_neg E Q.val⟩
  rw [← Finset.sum_fiberwise_of_maps_to'
    (fun Q hQ => Finset.mem_image_of_mem (fun R : G => xCoord R.val) hQ) f,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
  rw [hfiber Q hQ, Finset.sum_pair (hpair Q hQ)]
  ring

/-- Dividing each point contribution by two gives the sum over distinct x-coordinates. -/
theorem sum_xCoord_half [DecidableEq K] [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) (S : Finset G)
    (hzero : (0 : G) ∉ S) (hneg : ∀ Q ∈ S, -Q ∈ S)
    (hpair : ∀ Q ∈ S, Q ≠ -Q) (f : K → K) :
    (∑ Q ∈ S, f (xCoord Q.val) / 2) =
      ∑ u ∈ S.image (fun Q => xCoord Q.val), f u := by
  rw [← Finset.sum_div, sum_xCoord_image E G S hzero hneg hpair]
  exact mul_div_cancel_left₀ _ (NeZero.ne (2 : K))

/-- Removing an inverse pair removes exactly one x-coordinate from the image. -/
theorem image_xCoord_erase_pair [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) (S : Finset G) (hzero : (0 : G) ∉ S)
    (Q : G) (hQ : Q ∈ S) :
    ((S.erase Q).erase (-Q)).image (fun R => xCoord R.val) =
      (S.image (fun R => xCoord R.val)).erase (xCoord Q.val) := by
  have hnonzero (R : G) (hR : R ∈ S) : R.val ≠ 0 := by
    intro hz
    exact hzero ((Subtype.ext hz : R = 0) ▸ hR)
  ext u
  constructor
  · intro hu
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hu
    have hm : R ≠ -Q ∧ R ≠ Q ∧ R ∈ S := by simpa only [Finset.mem_erase] using hR
    apply Finset.mem_erase.mpr
    constructor
    · intro hx
      rcases (xCoord_eq_iff E (hnonzero R hm.2.2) (hnonzero Q hQ)).mp hx with h | h
      · exact hm.2.1 (Subtype.ext h)
      · exact hm.1 (Subtype.ext h)
    · exact Finset.mem_image_of_mem _ hm.2.2
  · intro hu
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hu
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hmem
    apply Finset.mem_image.mpr
    refine ⟨R, ?_, rfl⟩
    simp only [Finset.mem_erase]
    refine ⟨?_, ?_, hR⟩
    · intro h
      apply hne
      rw [h]
      exact xCoord_neg E Q.val
    · intro h
      exact hne (congrArg (fun R : G => xCoord R.val) h)

/-- The distinct x-coordinates of the nonzero points in a finite kernel. -/
noncomputable def kernelAbscissae [DecidableEq K] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G] : Finset K := by
  classical
  exact (Finset.univ.erase (0 : G)).image (fun Q => xCoord Q.val)

/-- Translation identities rewritten as sums over distinct kernel x-coordinates. -/
theorem regular_sums_image [DecidableEq K] [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (Q : G)
    {u v : K} (hu : E.toAffine.Nonsingular u v)
    (hval : Q.val = Affine.Point.some u v hu) :
    let a := fun x : K => 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆
    let c := fun x : K => 6 * x ^ 2 + E.b₂ * x + E.b₄
    (∑ w ∈ (kernelAbscissae E G).erase u, polePart (a w) (c w) w u) =
      u - xCoord (Q.val + Q.val) ∧
    a u * (∑ w ∈ (kernelAbscissae E G).erase u, poleSlope (a w) (c w) w u) =
      c u * (xCoord (Q.val + Q.val) - u) := by
  classical
  let a := fun x : K => 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆
  let c := fun x : K => 6 * x ^ 2 + E.b₂ * x + E.b₄
  let S := ((Finset.univ.erase (0 : G)).erase Q).erase (-Q)
  have hQ : Q ≠ 0 := by
    intro h
    exact Affine.Point.some_ne_zero hu (hval.symm.trans (congrArg Subtype.val h))
  have hQneg := hodd Q hQ
  have hzero : (0 : G) ∉ S := by simp [S]
  have hneg : ∀ R ∈ S, -R ∈ S := by
    intro R hR
    simpa [S, neg_eq_iff_eq_neg, and_comm, and_left_comm] using hR
  have hpair : ∀ R ∈ S, R ≠ -R := by
    intro R hR
    apply hodd R
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hR).2).2).1
  have himage : S.image (fun R => xCoord R.val) = (kernelAbscissae E G).erase u := by
    have h := image_xCoord_erase_pair E G (Finset.univ.erase 0) (by simp) Q (by simp [hQ])
    simpa only [S, kernelAbscissae, hval, xCoord] using h
  have hsum (f : K → K) :
      (∑ R ∈ S, f (xCoord R.val) / 2) =
        ∑ w ∈ (kernelAbscissae E G).erase u, f w := by
    rw [sum_xCoord_half E G S hzero hneg hpair, himage]
  have hp :
      (∑ R ∈ S,
        (tTerm E (xCoord R.val) / (u - xCoord R.val) +
          a (xCoord R.val) / (2 * (u - xCoord R.val) ^ 2))) =
        ∑ w ∈ (kernelAbscissae E G).erase u, polePart (a w) (c w) w u := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro R _
    dsimp [tTerm, polePart, a, c]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hs :
      (∑ R ∈ S,
        (-tTerm E (xCoord R.val) / (u - xCoord R.val) ^ 2 -
          a (xCoord R.val) / (u - xCoord R.val) ^ 3)) =
        ∑ w ∈ (kernelAbscissae E G).erase u, poleSlope (a w) (c w) w u := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro R _
    dsimp [tTerm, poleSlope, a, c]
    field_simp
  have hx := regular_xSum_at_kernel E G Q hu hval hQneg
  have hy := regular_slopeSum_x_identity E G Q hu hval hQneg
  change u + (∑ R ∈ S, _) = _ at hx
  change a u * (1 + ∑ R ∈ S, _) = a u + c u * _ at hy
  rw [hp] at hx
  rw [hs] at hy
  constructor
  · linear_combination hx
  · linear_combination hy

/-- The two local regular-sum identities for a kernel without nonzero two-torsion. -/
theorem kernel_pole_relations [DecidableEq K] [NeZero (2 : K)] (E : WeierstrassCurve K)
    (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) {u : K} (hu : u ∈ kernelAbscissae E G) :
    let a := fun x : K => 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆
    let c := fun x : K => 6 * x ^ 2 + E.b₂ * x + E.b₄
    a u * (E.b₂ + 12 * u) - c u ^ 2 =
      4 * a u * (∑ w ∈ (kernelAbscissae E G).erase u, polePart (a w) (c w) w u) ∧
    c u * (∑ w ∈ (kernelAbscissae E G).erase u, polePart (a w) (c w) w u) +
      a u * (∑ w ∈ (kernelAbscissae E G).erase u, poleSlope (a w) (c w) w u) = 0 := by
  classical
  obtain ⟨Q, hQ, hqu⟩ := Finset.mem_image.mp hu
  have hQ0 : Q ≠ 0 := (Finset.mem_erase.mp hQ).1
  have hq0 : Q.val ≠ 0 := fun h => hQ0 (Subtype.ext h)
  rcases hval : Q.val with _ | ⟨x, y, hxy⟩
  · exact (hq0 hval).elim
  · have hxu : x = u := by simpa only [hval, xCoord] using hqu
    rw [← hxu]
    have hp := regular_sums_image E G hodd Q hxy hval
    have hv : y ≠ E.toAffine.negY x y := by
      intro h
      apply hodd Q hQ0
      apply Subtype.ext
      change Q.val = -Q.val
      rw [hval, Affine.Point.neg_some]
      congr 1
    have hd := duplication_pole_identity E hxy hv
    rw [← hval] at hd
    dsimp only at hp ⊢
    rw [hp.1]
    constructor
    · linear_combination hd
    · linear_combination hp.2

/-- The second-order differential identity for the rational sum attached to the kernel. -/
theorem kernel_pole_differential_eq_zero [DecidableEq K] [NeZero (2 : K)]
    (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) (x : K) (hx : x ∉ kernelAbscissae E G) :
    let a := fun u : K => 4 * u ^ 3 + E.b₂ * u ^ 2 + 2 * E.b₄ * u + E.b₆
    let c := fun u : K => 6 * u ^ 2 + E.b₂ * u + E.b₄
    let S := kernelAbscissae E G
    let X := x + ∑ u ∈ S, polePart (a u) (c u) u x
    let D := 1 + ∑ u ∈ S, poleSlope (a u) (c u) u x
    let DD := ∑ u ∈ S, poleCurvature (a u) (c u) u x
    2 * a x * DD + 2 * c x * D - 12 * X ^ 2 - 2 * E.b₂ * X - 2 * E.b₄ +
      20 * (∑ u ∈ S, c u) = 0 := by
  apply sum_polePart_differential_eq_zero
  · intro u hu h
    exact hx (h ▸ hu)
  · intro u hu
    exact (kernel_pole_relations E G hodd hu).1
  · intro u hu
    exact (kernel_pole_relations E G hodd hu).2

/-- A nonzero point killed by an odd integer cannot be fixed by negation. -/
theorem ne_neg_of_odd_nsmul {A : Type*} [AddCommGroup A] {n : ℕ} (hn : Odd n)
    {Q : A} (hQ : Q ≠ 0) (hkill : n • Q = 0) : Q ≠ -Q := by
  intro heq
  have htwo : (2 : ℕ) • Q = 0 := by
    rw [two_nsmul]
    exact add_eq_zero_iff_eq_neg.mpr heq
  obtain ⟨k, hk⟩ := hn
  rw [hk, add_nsmul, mul_nsmul, htwo, nsmul_zero, one_nsmul, zero_add] at hkill
  exact hQ hkill

end WeierstrassCurve.Velu
