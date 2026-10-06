/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicSecantProjective

/-! # Infinity-output comparison for the descended affine addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The homogeneous chord underlying a vertical addition piece. -/
def pairChordPoint (b : Bool) : Fin 3 → AffinePairRing W :=
  ![pairChordX W b, pairChordY W b, pairChordT W b ^ 3]

theorem verticalSum_normalized (b : Bool) (i : Fin 3) :
    chartPointCoords W true (verticalSum W b) i =
      verticalRestriction W b (pairChordPoint W b i) * verticalInv W b := by
  fin_cases i
  · exact verticalSum_coord W b 0
  · exact (IsLocalization.Away.mul_invSelf (S := VerticalRing W b) (pairChordY W b)).symm
  · exact verticalSum_coord W b 1

theorem verticalSum_normalized_map (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S] (f : VerticalRing W b →ₐ[R] S) (i : Fin 3) :
    chartPointCoords W true (f.comp (verticalSum W b)) i =
      f (verticalRestriction W b (pairChordPoint W b i)) * f (verticalInv W b) := by
  rw [chartPointCoords_baseChange]
  change f (chartPointCoords W true (verticalSum W b) i) = _
  rw [verticalSum_normalized, map_mul]

theorem affineAddition_after_vertical [W.IsElliptic] (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S] (f : VerticalRing W b →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (f.comp (verticalRestriction W b)).toRingHom) ≫
        affineAddition W =
      Spec.map (CommRingCat.ofHom (f.comp (verticalSum W b)).toRingHom) ≫ infinityChart W := by
  have h : Spec.map (CommRingCat.ofHom (verticalRestriction W b).toRingHom) ≫
      affineAddition W = verticalAddition W b := by
    cases b
    · exact affineAddition_restrict W 2
    · exact affineAddition_restrict W 3
  change Spec.map (CommRingCat.ofHom (verticalRestriction W b).toRingHom ≫
    CommRingCat.ofHom f.toRingHom) ≫ affineAddition W = _
  rw [Spec.map_comp, Category.assoc, h]
  unfold verticalAddition
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Any infinity-chart normalization of either chord agrees with the full
affine-input addition. The normalized Y-coordinate supplies the required unit. -/
theorem affineAddition_chord_comparison [W.IsElliptic] (b : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : AffinePairRing W →ₐ[R] S) (g : Ring W true →ₐ[R] S) (c : S)
    (hg : ∀ i, chartPointCoords W true g i = f (pairChordPoint W b i) * c) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ affineAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityChart W := by
  have hy : f (pairChordY W b) * c = 1 := (hg 1).symm
  let k : VerticalRing W b →ₐ[R] S :=
    IsLocalization.Away.liftAlgHom (pairChordY W b) (f := f)
      (isUnit_iff_exists_inv.mpr ⟨c, hy⟩)
  have hk (x : AffinePairRing W) : k (verticalRestriction W b x) = f x := by
    simp [k, verticalRestriction]
  have hkf : k.comp (verticalRestriction W b) = f := AlgHom.ext hk
  have he := affineAddition_after_vertical W b k
  rw [hkf] at he
  apply he.trans
  apply chart_point_agreement_of_scaled W true true _ _
    (fun i ↦ f (pairChordPoint W b i)) (fun i ↦ f (pairChordPoint W b i))
    (k (verticalInv W b)) c
  · intro i
    exact (verticalSum_normalized_map W b k i).trans
      (congrArg (· * k (verticalInv W b)) (hk _))
  · exact hg
  · intro i j
    rfl

theorem chartPairSum_affine :
    chartPairSum W false false = -pairChordPoint W false :=
  projective_addXYZ_affine _ (pair_input_equation W false) (pair_input_equation W true)

/-- A projective normalization into the infinity chart also agrees with the
descended affine law, including sums equal to infinity. -/
theorem affineAddition_projective_infinity_comparison [W.IsElliptic]
    {S : Type u} [CommRing S] [Algebra R S]
    (a b : Ring W false →ₐ[R] S) (g : Ring W true →ₐ[R] S) (c : S)
    (hg : ∀ i, chartPointCoords W true g i =
      (W.map (algebraMap R S)).toProjective.addXYZ
        (chartPointCoords W false a) (chartPointCoords W false b) i * c) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
        affineAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ infinityChart W := by
  let f := Algebra.TensorProduct.productMap a b
  have hl : f ∘ chartPairLeft W false false = chartPointCoords W false a := by
    have h := chartPointCoords_baseChange W false f (pairInput W false)
    have ha : f.comp (pairInput W false) = a := Algebra.TensorProduct.productMap_left a b
    rw [ha] at h
    exact h.symm
  have hr : f ∘ chartPairRight W false false = chartPointCoords W false b := by
    have h := chartPointCoords_baseChange W false f (pairInput W true)
    have hb : f.comp (pairInput W true) = b := Algebra.TensorProduct.productMap_right a b
    rw [hb] at h
    exact h.symm
  have hp := Projective.baseChange_addXYZ (W' := W.toProjective) f
    (chartPairLeft W false false) (chartPairRight W false false)
  rw [hl, hr] at hp
  apply affineAddition_chord_comparison W false f g (-c)
  intro i
  have hi := congrFun hp i
  change (W.map (algebraMap R S)).toProjective.addXYZ
    (chartPointCoords W false a) (chartPointCoords W false b) i =
      f (chartPairSum W false false i) at hi
  rw [chartPairSum_affine] at hi
  change _ = f (-pairChordPoint W false i) at hi
  rw [map_neg] at hi
  rw [hg, hi]
  ring

end WeierstrassCurve.CubicCharts
