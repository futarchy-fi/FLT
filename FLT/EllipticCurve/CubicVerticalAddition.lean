/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicChord

/-! # Local addition with values in the infinity chart

Two homogeneous chord formulas, for secants and for tangents, give actual
morphisms after inverting their output Y-coordinate. These opens include
opposite affine points and vertical tangents, respectively. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem pair_input_equation (b : Bool) :
    (W.map (algebraMap R (AffinePairRing W))).toAffine.Equation
      (pairCoord W b 0) (pairCoord W b 1) :=
  chart_hom_equation W (pairInput W b)

/-- Numerator of the secant (false) or divided-difference (true) slope. -/
def pairChordS (b : Bool) : AffinePairRing W :=
  if b then chordNumerator (W.map (algebraMap R (AffinePairRing W)))
    (pairCoord W false 0) (pairCoord W true 0) (pairCoord W false 1)
  else pairCoord W true 1 - pairCoord W false 1

/-- Denominator of the secant (false) or divided-difference (true) slope. -/
def pairChordT (b : Bool) : AffinePairRing W :=
  if b then tangentDenominator W else secantDenominator W

/-- Homogeneous X-coordinate of either chord construction on the product. -/
def pairChordX (b : Bool) : AffinePairRing W :=
  chordX (W.map (algebraMap R (AffinePairRing W)))
    (pairCoord W false 0) (pairCoord W true 0) (pairChordS W b) (pairChordT W b)

/-- Homogeneous Y-coordinate of either chord construction on the product. -/
def pairChordY (b : Bool) : AffinePairRing W :=
  chordY (W.map (algebraMap R (AffinePairRing W)))
    (pairCoord W false 0) (pairCoord W true 0) (pairCoord W false 1)
    (pairChordS W b) (pairChordT W b)

theorem pairChord_equation (b : Bool) :
    (W.map (algebraMap R (AffinePairRing W))).toProjective.Equation
      ![pairChordX W b, pairChordY W b, pairChordT W b ^ 3] := by
  apply chord_projective_equation _ (pair_input_equation W false)
  cases b
  · exact secant_chord_obstruction _ (pair_input_equation W false) (pair_input_equation W true)
  · exact tangent_chord_obstruction _ (pair_input_equation W false) (pair_input_equation W true)

/-- The open where the homogeneous sum belongs to the infinity chart. -/
abbrev VerticalRing (b : Bool) := Localization.Away (pairChordY W b)

/-- Restriction from the chart product to a vertical addition domain. -/
def verticalRestriction (b : Bool) : AffinePairRing W →ₐ[R] VerticalRing W b :=
  IsScalarTower.toAlgHom R (AffinePairRing W) (VerticalRing W b)

/-- Inverse of the homogeneous output Y-coordinate. -/
def verticalInv (b : Bool) : VerticalRing W b := IsLocalization.Away.invSelf (pairChordY W b)

/-- Normalized coordinates of the sum in the infinity chart. -/
def verticalSumCoords (b : Bool) : Fin 2 → VerticalRing W b :=
  ![verticalRestriction W b (pairChordX W b) * verticalInv W b,
    verticalRestriction W b (pairChordT W b ^ 3) * verticalInv W b]

theorem verticalSum_root (b : Bool) :
    aeval (verticalSumCoords W b) (equation W true) = 0 :=
  infinity_normalize_algHom W (verticalRestriction W b) (pairChord_equation W b)
    (IsLocalization.Away.mul_invSelf (S := VerticalRing W b) (pairChordY W b))

/-- Pullback on functions for the normalized homogeneous sum. -/
def verticalSum (b : Bool) : Ring W true →ₐ[R] VerticalRing W b :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W true}) (aeval (verticalSumCoords W b)) (by
    change Ideal.span {equation W true} ≤
      RingHom.ker (aeval (verticalSumCoords W b) :
        MvPolynomial (Fin 2) R →ₐ[R] VerticalRing W b).toRingHom
    rw [Ideal.span_le]
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact verticalSum_root W b)

@[simp] theorem verticalSum_coord (b : Bool) (i : Fin 2) :
    verticalSum W b (coord W true i) = verticalSumCoords W b i := by
  change aeval _ (X i) = _
  simp

/-- Both vertical domains embed as opens of the cubic product. -/
def verticalInclusion (b : Bool) :
    Spec (.of (VerticalRing W b)) ⟶ pullback (toBase W) (toBase W) :=
  Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W b))) ≫
    (pullbackSpecIso R (Ring W false) (Ring W false)).inv ≫ affinePairInclusion W

instance verticalInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (verticalInclusion W b) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W b)))) :=
    IsOpenImmersion.of_isLocalization (pairChordY W b)
  unfold verticalInclusion
  infer_instance

/-- Addition with target in the infinity chart, on the specified homogeneous open. -/
def verticalAddition (b : Bool) : Spec (.of (VerticalRing W b)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (verticalSum W b).toRingHom) ≫ infinityChart W

@[reassoc (attr := simp)] theorem verticalAddition_toBase (b : Bool) :
    verticalAddition W b ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (VerticalRing W b))) := by
  unfold verticalAddition
  rw [Category.assoc, infinityChart_toBase]
  unfold chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (verticalSum W b).comp_algebraMap

end WeierstrassCurve.CubicCharts
