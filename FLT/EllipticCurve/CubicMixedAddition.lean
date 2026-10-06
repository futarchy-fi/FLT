/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAdditionCover
public import FLT.EllipticCurve.CubicChartPoint
public import FLT.EllipticCurve.CubicVerticalOverlap

/-! # Mixed-chart compatibility for chord addition

The homogeneous chord identities give the coordinate transition needed to
compare an ordinary-output formula with an infinity-output formula. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The homogeneous y-coordinate gives the usual affine addition formula when t is a unit. -/
theorem chordY_affine {x₁ x₂ y₁ s t v : R} (ht : t * v = 1) :
    chordY W x₁ x₂ y₁ s t * v ^ 3 = W.toAffine.addY x₁ x₂ y₁ (s * v) := by
  unfold chordY chordXNumerator Affine.addY Affine.negY Affine.negAddY Affine.addX
  linear_combination
    (-2 * W.a₁ * s ^ 2 * v ^ 2 +
      (W.a₂ + 2 * x₁ + x₂ - W.a₁ ^ 2) * s * v * (t * v + 1) +
      (W.a₁ * (W.a₂ + x₁ + x₂) - y₁ - W.a₃) *
        ((t * v) ^ 2 + t * v + 1)) * ht

/-- Proportional chord parameters give proportional X and Z output coordinates. -/
theorem chord_cross_xz (x₁ x₂ s t u v : R) (h : s * v = u * t) :
    chordX W x₁ x₂ s t * v ^ 3 = chordX W x₁ x₂ u v * t ^ 3 := by
  unfold chordX chordXNumerator
  linear_combination (t * v * (s * v + u * t) + W.a₁ * t ^ 2 * v ^ 2) * h

/-- The normalized affine and infinity outputs satisfy the y/z transition identity. -/
theorem chord_mixed_y {x₁ x₂ y₁ s t u v ti yi : R}
    (ht : t * ti = 1) (hy : chordY W x₁ x₂ y₁ u v * yi = 1)
    (h : s * v = u * t) :
    W.toAffine.addY x₁ x₂ y₁ (s * ti) * (v ^ 3 * yi) = 1 := by
  rw [← chordY_affine W ht]
  calc
    _ = (v ^ 3 * chordY W x₁ x₂ y₁ s t) * (ti ^ 3 * yi) := by ring
    _ = (t ^ 3 * chordY W x₁ x₂ y₁ u v) * (ti ^ 3 * yi) := by
      rw [← chord_cross_zy W x₁ x₂ y₁ s t u v h]
    _ = (t * ti) ^ 3 * (chordY W x₁ x₂ y₁ u v * yi) := by ring
    _ = 1 := by rw [ht, hy, one_pow, one_mul]

/-- The normalized affine and infinity outputs satisfy the x/y transition identity. -/
theorem chord_mixed_x {x₁ x₂ s t u v ti yi : R}
    (ht : t * ti = 1) (h : s * v = u * t) :
    W.toAffine.addX x₁ x₂ (s * ti) * (v ^ 3 * yi) =
      chordX W x₁ x₂ u v * yi := by
  rw [← chordX_affine W ht]
  calc
    _ = (chordX W x₁ x₂ s t * v ^ 3) * (ti ^ 3 * yi) := by ring
    _ = (chordX W x₁ x₂ u v * t ^ 3) * (ti ^ 3 * yi) := by
      rw [chord_cross_xz W x₁ x₂ s t u v h]
    _ = (chordX W x₁ x₂ u v * yi) * (t * ti) ^ 3 := by ring
    _ = _ := by rw [ht, one_pow, mul_one]

/-- Mixed chord formulas define the same scheme morphism whenever their chord parameters
are proportional and the chosen target coordinates are invertible. -/
theorem chord_mixed_scheme_agreement {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W false →ₐ[R] S) (g : Ring W true →ₐ[R] S)
    (x₁ x₂ y₁ s t u v ti yi : S)
    (ht : t * ti = 1)
    (hy : chordY (W.map (algebraMap R S)) x₁ x₂ y₁ u v * yi = 1)
    (h : s * v = u * t)
    (hfx : f (coord W false 0) =
      (W.map (algebraMap R S)).toAffine.addX x₁ x₂ (s * ti))
    (hfy : f (coord W false 1) =
      (W.map (algebraMap R S)).toAffine.addY x₁ x₂ y₁ (s * ti))
    (hgu : g (coord W true 0) = chordX (W.map (algebraMap R S)) x₁ x₂ u v * yi)
    (hgv : g (coord W true 1) = v ^ 3 * yi) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ affineChart W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityChart W := by
  apply chart_point_agreement W f g
  · rw [hfy, hgv]
    exact chord_mixed_y _ ht hy h
  · rw [hfx, hgu, hgv]
    exact chord_mixed_x _ ht h

/-- Affine x-addition commutes with coefficient extension. -/
theorem addX_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (x₁ x₂ l : A) :
    f ((W.map (algebraMap R A)).toAffine.addX x₁ x₂ l) =
      (W.map (algebraMap R B)).toAffine.addX (f x₁) (f x₂) (f l) := by
  simp [Affine.addX, WeierstrassCurve.map]

/-- Affine y-addition commutes with coefficient extension. -/
theorem addY_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (x₁ x₂ y₁ l : A) :
    f ((W.map (algebraMap R A)).toAffine.addY x₁ x₂ y₁ l) =
      (W.map (algebraMap R B)).toAffine.addY (f x₁) (f x₂) (f y₁) (f l) := by
  simp [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX, WeierstrassCurve.map]

/-- The homogeneous X-coordinate commutes with coefficient extension. -/
theorem chordX_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (x₁ x₂ s t : A) :
    f (chordX (W.map (algebraMap R A)) x₁ x₂ s t) =
      chordX (W.map (algebraMap R B)) (f x₁) (f x₂) (f s) (f t) := by
  simp [chordX, chordXNumerator, WeierstrassCurve.map]


private theorem map_cube {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (x : A) : f (x ^ 3) = f x ^ 3 :=
  map_pow f x 3

/-- A chord map in the ordinary chart agrees with either vertical chart formula,
after any common restriction of the input pair. -/
theorem ordinary_vertical_agreement {A S : Type u} [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (k b : Bool)
    (j : AffinePairRing W →ₐ[R] A) (p : Ring W false →ₐ[R] A) (ti : A)
    (htA : j (pairChordT W k) * ti = 1)
    (hxA : p (coord W false 0) = (W.map (algebraMap R A)).toAffine.addX
      (j (pairCoord W false 0)) (j (pairCoord W true 0)) (j (pairChordS W k) * ti))
    (hyA : p (coord W false 1) = (W.map (algebraMap R A)).toAffine.addY
      (j (pairCoord W false 0)) (j (pairCoord W true 0)) (j (pairCoord W false 1))
      (j (pairChordS W k) * ti))
    (f : A →ₐ[R] S) (g : VerticalRing W b →ₐ[R] S)
    (h : f.comp j = g.comp (verticalRestriction W b)) :
    Spec.map (CommRingCat.ofHom (f.comp p).toRingHom) ≫ affineChart W =
      Spec.map (CommRingCat.ofHom (g.comp (verticalSum W b)).toRingHom) ≫ infinityChart W := by
  let c := f.comp j
  have hv (x : AffinePairRing W) : c x = g (verticalRestriction W b x) :=
    DFunLike.congr_fun h x
  have ht : c (pairChordT W k) * f ti = 1 := by
    have hh := congrArg f htA
    simp only [map_mul, map_one] at hh
    exact hh
  have hy :
      chordY (W.map (algebraMap R S)) (c (pairCoord W false 0)) (c (pairCoord W true 0))
        (c (pairCoord W false 1)) (c (pairChordS W b)) (c (pairChordT W b)) *
          g (verticalInv W b) = 1 := by
    have hh := congrArg g
      (IsLocalization.Away.mul_invSelf (S := VerticalRing W b) (pairChordY W b))
    simp only [map_mul, map_one] at hh
    change g (verticalRestriction W b (pairChordY W b)) * g (verticalInv W b) = 1 at hh
    rw [← hv] at hh
    have hm := chordY_baseChange W c (pairCoord W false 0) (pairCoord W true 0)
      (pairCoord W false 1) (pairChordS W b) (pairChordT W b)
    change c (pairChordY W b) = _ at hm
    rw [hm] at hh
    exact hh
  have hp : c (pairChordS W k) * c (pairChordT W b) =
      c (pairChordS W b) * c (pairChordT W k) := by
    have hh : pairChordS W k * pairChordT W b = pairChordS W b * pairChordT W k := by
      cases k <;> cases b
      · rfl
      · exact pairChord_relation W
      · exact (pairChord_relation W).symm
      · rfl
    have hc := congrArg c hh
    simpa only [map_mul] using hc
  apply chord_mixed_scheme_agreement W (f.comp p) (g.comp (verticalSum W b))
    (c (pairCoord W false 0)) (c (pairCoord W true 0)) (c (pairCoord W false 1))
    (c (pairChordS W k)) (c (pairChordT W k))
    (c (pairChordS W b)) (c (pairChordT W b)) (f ti) (g (verticalInv W b))
    ht hy hp
  · change f (p (coord W false 0)) = _
    rw [hxA, addX_baseChange W f, map_mul]
    rfl
  · change f (p (coord W false 1)) = _
    rw [hyA, addY_baseChange W f, map_mul]
    rfl
  · change g (verticalSum W b (coord W true 0)) = _
    rw [verticalSum_coord]
    change g (verticalRestriction W b (pairChordX W b) * verticalInv W b) = _
    rw [map_mul, ← hv]
    exact congrArg (fun z ↦ z * g (verticalInv W b))
      (chordX_baseChange W c (pairCoord W false 0) (pairCoord W true 0)
        (pairChordS W b) (pairChordT W b))
  · change g (verticalSum W b (coord W true 1)) = _
    rw [verticalSum_coord]
    change g (verticalRestriction W b (pairChordT W b ^ 3) * verticalInv W b) = _
    rw [map_mul, ← hv]
    exact congrArg (fun z ↦ z * g (verticalInv W b))
      (map_cube (A := AffinePairRing W) c (pairChordT W b))

/-- Secant addition agrees with both infinity-output chord maps on common restrictions. -/
theorem secant_vertical_agreement {S : Type u} [CommRing S] [Algebra R S] (b : Bool)
    (f : SecantRing W →ₐ[R] S) (g : VerticalRing W b →ₐ[R] S)
    (h : f.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)) =
      g.comp (verticalRestriction W b)) :
    Spec.map (CommRingCat.ofHom (f.comp (secantSum W)).toRingHom) ≫ affineChart W =
      Spec.map (CommRingCat.ofHom (g.comp (verticalSum W b)).toRingHom) ≫ infinityChart W := by
  let j := IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)
  have hs : j (pairChordS W false) * secantInv W = secantSlope W := by
    change j (pairCoord W true 1 - pairCoord W false 1) * secantInv W = _
    rw [map_sub]
    rfl
  apply ordinary_vertical_agreement W false b j (secantSum W) (secantInv W) ?_ ?_ ?_ f g h
  · exact IsLocalization.Away.mul_invSelf (S := SecantRing W) (secantDenominator W)
  · rw [hs, secantSum_coord]
    rfl
  · rw [hs, secantSum_coord]
    rfl

/-- Nonvertical tangent addition agrees with both infinity-output chord maps. -/
theorem tangent_vertical_agreement {S : Type u} [CommRing S] [Algebra R S] (b : Bool)
    (f : TangentRing W →ₐ[R] S) (g : VerticalRing W b →ₐ[R] S)
    (h : f.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W)) =
      g.comp (verticalRestriction W b)) :
    Spec.map (CommRingCat.ofHom (f.comp (tangentSum W)).toRingHom) ≫ affineChart W =
      Spec.map (CommRingCat.ofHom (g.comp (verticalSum W b)).toRingHom) ≫ infinityChart W := by
  let j := IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W)
  have hs : j (pairChordS W true) * tangentInv W = tangentSlope W :=
    congrArg (fun z ↦ z * tangentInv W)
      (chordNumerator_baseChange W j (pairCoord W false 0) (pairCoord W true 0)
        (pairCoord W false 1))
  apply ordinary_vertical_agreement W true b j (tangentSum W) (tangentInv W) ?_ ?_ ?_ f g h
  · exact IsLocalization.Away.mul_invSelf (S := TangentRing W) (tangentDenominator W)
  · rw [hs, tangentSum_coord]
    rfl
  · rw [hs, tangentSum_coord]
    rfl

end WeierstrassCurve.CubicCharts
