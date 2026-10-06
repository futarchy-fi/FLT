/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveComparison
public import FLT.EllipticCurve.CubicMixedAddition
public import FLT.EllipticCurve.CubicAffineAddition

/-! # The projective law agrees with affine secant addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem projective_addXYZ_affine {x₁ y₁ x₂ y₂ : R}
    (hP : W.toAffine.Equation x₁ y₁) (hQ : W.toAffine.Equation x₂ y₂) :
    W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1] =
      -![chordX W x₁ x₂ (y₂ - y₁) (x₂ - x₁),
        chordY W x₁ x₂ y₁ (y₂ - y₁) (x₂ - x₁), (x₂ - x₁) ^ 3] := by
  have hp : W.toProjective.Equation ![x₁, y₁, 1] := (Projective.equation_some ..).mpr hP
  have hq : W.toProjective.Equation ![x₂, y₂, 1] := (Projective.equation_some ..).mpr hQ
  have hx := Projective.addX_eq' hp hq
  have hy := Projective.negAddY_eq' hp hq
  have hz := Projective.addZ_eq' hp hq
  simp only [Projective.fin3_def_ext, mul_one, one_pow] at hx hy hz
  ext i
  fin_cases i
  · change W.toProjective.addX _ _ = -chordX W x₁ x₂ (y₂ - y₁) (x₂ - x₁)
    unfold chordX chordXNumerator
    linear_combination hx
  · change W.toProjective.addY _ _ = -chordY W x₁ x₂ y₁ (y₂ - y₁) (x₂ - x₁)
    rw [Projective.addY, Projective.negY_eq]
    unfold chordY chordXNumerator
    linear_combination -hy - W.a₁ * hx - W.a₃ * hz
  · change W.toProjective.addZ _ _ = -(x₂ - x₁) ^ 3
    linear_combination hz

/-- On a secant domain the normalized projective coordinates are the existing affine sum. -/
theorem projective_addXYZ_secant {x₁ y₁ x₂ y₂ t : R}
    (hP : W.toAffine.Equation x₁ y₁) (hQ : W.toAffine.Equation x₂ y₂)
    (ht : (x₂ - x₁) * t = 1) :
    (fun i ↦ W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1] i * (-t ^ 3)) =
      ![W.toAffine.addX x₁ x₂ ((y₂ - y₁) * t),
        W.toAffine.addY x₁ x₂ y₁ ((y₂ - y₁) * t), 1] := by
  rw [projective_addXYZ_affine W hP hQ]
  ext i
  fin_cases i
  · change -chordX W x₁ x₂ (y₂ - y₁) (x₂ - x₁) * (-t ^ 3) = _
    rw [neg_mul_neg]
    exact chordX_affine W ht
  · change -chordY W x₁ x₂ y₁ (y₂ - y₁) (x₂ - x₁) * (-t ^ 3) = _
    rw [neg_mul_neg]
    exact chordY_affine W ht
  · change -(x₂ - x₁) ^ 3 * (-t ^ 3) = 1
    rw [neg_mul_neg, ← mul_pow, ht, one_pow]

theorem secantSum_normalized (i : Fin 3) :
    chartPointCoords W false (secantSum W) i =
      (W.map (algebraMap R (SecantRing W))).toProjective.addXYZ
        ![secantCoord W false 0, secantCoord W false 1, 1]
        ![secantCoord W true 0, secantCoord W true 1, 1] i * (-secantInv W ^ 3) := by
  have h := projective_addXYZ_secant (W.map (algebraMap R (SecantRing W)))
    (secant_input_equation W false) (secant_input_equation W true)
    (secant_difference_mul_inv W)
  have hi := (congrFun h i).symm
  fin_cases i <;>
    simpa [chartPointCoords, secantSum_coord, secantSumCoords, secantSlope] using hi

/-- The glued affine addition restricts to the secant formula after any coefficient map. -/
theorem affineAddition_after_secant [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S] (f : SecantRing W →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom
        (f.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W))).toRingHom) ≫
        affineAddition W =
      Spec.map (CommRingCat.ofHom (f.comp (secantSum W)).toRingHom) ≫ affineChart W := by
  change Spec.map
      (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W)) ≫
        CommRingCat.ofHom f.toRingHom) ≫ affineAddition W = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    affineAdditionInclusion W 0 ≫ affineAddition W = _
  rw [affineAddition_restrict]
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ secantAddition W = _
  unfold secantAddition
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem secantSum_normalized_map {S : Type u} [CommRing S] [Algebra R S]
    (f : SecantRing W →ₐ[R] S) (i : Fin 3) :
    chartPointCoords W false (f.comp (secantSum W)) i =
      (W.map (algebraMap R S)).toProjective.addXYZ
        (chartPointCoords W false (f.comp (secantInput W false)))
        (chartPointCoords W false (f.comp (secantInput W true))) i *
          (-(f (secantInv W)) ^ 3) := by
  have hp := Projective.baseChange_addXYZ (W' := W.toProjective) f
    (chartPointCoords W false (secantInput W false))
    (chartPointCoords W false (secantInput W true))
  rw [← chartPointCoords_baseChange, ← chartPointCoords_baseChange] at hp
  have hn := congrArg f (secantSum_normalized W i)
  simp only [map_mul, map_neg, map_pow] at hn
  rw [chartPointCoords_baseChange]
  change f (chartPointCoords W false (secantSum W) i) = _
  rw [hn]
  congr 1
  exact (congrFun hp i).symm

/-- An affine normalization of the homogeneous secant law agrees with the glued
affine addition. Its normalized Z-coordinate itself forces the secant denominator
to be a unit, so no extra generic-position hypothesis is assumed. -/
theorem affineAddition_projective_comparison [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (a b g : Ring W false →ₐ[R] S) (c : S)
    (hg : ∀ i, chartPointCoords W false g i =
      (W.map (algebraMap R S)).toProjective.addXYZ
        (chartPointCoords W false a) (chartPointCoords W false b) i * c) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
        affineAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ affineChart W := by
  let f : AffinePairRing W →ₐ[R] S := Algebra.TensorProduct.productMap a b
  let d := b (coord W false 0) - a (coord W false 0)
  have hz := congrFun (projective_addXYZ_affine (W.map (algebraMap R S))
    (chart_hom_equation W a) (chart_hom_equation W b)) 2
  change (W.map (algebraMap R S)).toProjective.addXYZ
    (chartPointCoords W false a) (chartPointCoords W false b) 2 = -d ^ 3 at hz
  have hc := hg 2
  change 1 = _ at hc
  rw [hz] at hc
  have ht : d * (-c * d ^ 2) = 1 := by linear_combination -hc
  have hleft (x : Ring W false) :
      f ((Algebra.TensorProduct.includeLeft : Ring W false →ₐ[R] AffinePairRing W) x) = a x :=
    DFunLike.congr_fun (Algebra.TensorProduct.productMap_left a b) x
  have hright (x : Ring W false) :
      f ((Algebra.TensorProduct.includeRight : Ring W false →ₐ[R] AffinePairRing W) x) = b x :=
    DFunLike.congr_fun (Algebra.TensorProduct.productMap_right a b) x
  have hd : f (secantDenominator W) = d := by
    unfold secantDenominator
    rw [map_sub, hright, hleft]
  let k : SecantRing W →ₐ[R] S :=
    IsLocalization.Away.liftAlgHom (secantDenominator W) (f := f)
      (isUnit_iff_exists_inv.mpr ⟨-c * d ^ 2, by rw [hd]; exact ht⟩)
  have hk (x : AffinePairRing W) :
      k ((IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)) x) = f x := by
    simp [k, IsLocalization.Away.liftAlgHom_apply]
  have hka : k.comp (secantInput W false) = a := by
    apply AlgHom.ext
    intro x
    exact (hk _).trans (hleft x)
  have hkb : k.comp (secantInput W true) = b := by
    apply AlgHom.ext
    intro x
    exact (hk _).trans (hright x)
  have hkf : k.comp (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)) = f :=
    AlgHom.ext hk
  have he := affineAddition_after_secant W k
  rw [hkf] at he
  apply he.trans
  apply chart_point_agreement_of_scaled W false false _ _
    ((W.map (algebraMap R S)).toProjective.addXYZ
      (chartPointCoords W false a) (chartPointCoords W false b))
    ((W.map (algebraMap R S)).toProjective.addXYZ
      (chartPointCoords W false a) (chartPointCoords W false b))
    (-(k (secantInv W)) ^ 3) c
  · intro i
    have h := secantSum_normalized_map W k i
    rw [hka, hkb] at h
    exact h
  · exact hg
  · intro i j
    rfl

end WeierstrassCurve.CubicCharts
