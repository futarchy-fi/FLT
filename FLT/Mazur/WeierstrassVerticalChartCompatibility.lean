/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVerticalAdditionCharts

/-!
# Equality of the normalized vertical addition maps on overlaps

The two reciprocal slopes coincide after a common restriction of the affine
product. Their homogeneous outputs and their normalizing inverses then agree,
so the actual algebra maps from the Y = 1 chart agree as well.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (W : WeierstrassCurve R)

/-- Reciprocal homogeneous coordinates commute with every algebra specialization. -/
theorem reciprocalCoordinates_map (f : AffineProduct W →ₐ[R] S) (m : S)
    (g : S →ₐ[R] T) (i : Fin 3) :
    g (reciprocalCoordinates W f m i) =
      reciprocalCoordinates W (g.comp f) (g m) i := by
  fin_cases i <;>
    simp [reciprocalCoordinates, reciprocalXYZ, reciprocalH, AlgHom.commutes]

/-- The base restriction for the normalized vertical secant chart. -/
def verticalSecantRestriction : AffineProduct W →ₐ[R]
    ReciprocalTargetOpen W (ratioRestriction W (verticalSecantDenominator W))
      (verticalSecantSlope W) :=
  (reciprocalTargetRestriction W _ (verticalSecantSlope W)).comp
    (ratioRestriction W (verticalSecantDenominator W))

/-- The base restriction for the normalized vertical tangent chart. -/
def verticalTangentRestriction : AffineProduct W →ₐ[R]
    ReciprocalTargetOpen W (ratioRestriction W (tangentNumerator W)) (verticalTangentSlope W) :=
  (reciprocalTargetRestriction W _ (verticalTangentSlope W)).comp
    (ratioRestriction W (tangentNumerator W))

variable
  (f : ReciprocalTargetOpen W (ratioRestriction W (verticalSecantDenominator W))
    (verticalSecantSlope W) →ₐ[R] S)
  (g : ReciprocalTargetOpen W (ratioRestriction W (tangentNumerator W))
    (verticalTangentSlope W) →ₐ[R] S)
  (hbase : f.comp (verticalSecantRestriction W) = g.comp (verticalTangentRestriction W))

include hbase in
/-- The regular reciprocal slopes agree on every common restriction of the two domains. -/
theorem verticalSlope_chart_compatibility :
    f (reciprocalTargetRestriction W _ (verticalSecantSlope W) (verticalSecantSlope W)) =
      g (reciprocalTargetRestriction W _ (verticalTangentSlope W) (verticalTangentSlope W)) := by
  let fs := f.comp (reciprocalTargetRestriction W _ (verticalSecantSlope W))
  let gs := g.comp (reciprocalTargetRestriction W _ (verticalTangentSlope W))
  have hb (a) : fs (ratioRestriction W (verticalSecantDenominator W) a) =
      gs (ratioRestriction W (tangentNumerator W) a) := DFunLike.congr_fun hbase a
  have hu := (IsLocalization.Away.algebraMap_isUnit (verticalSecantDenominator W)
    (S := RatioChart W (verticalSecantDenominator W))).map fs
  change IsUnit (fs (ratioRestriction W (verticalSecantDenominator W)
    (verticalSecantDenominator W))) at hu
  have hs := congrArg fs (ratioSlope_mul W (verticalSecantDenominator W) (secantDenominator W))
  have ht' : verticalTangentSlope W *
      ratioRestriction W (tangentNumerator W) (verticalSecantDenominator W) =
      ratioRestriction W (tangentNumerator W) (secantDenominator W) := by
    simpa only [map_verticalSecantDenominator, map_secantDenominator]
      using verticalTangent_line W
  have ht := congrArg gs ht'
  simp only [map_mul, ← hb] at hs ht
  change fs (verticalSecantSlope W) = gs (verticalTangentSlope W)
  exact hu.mul_left_inj.mp (hs.trans ht.symm)

include hbase in
/-- The two actual normalized maps into the infinity chart agree on their overlaps. -/
theorem verticalAddition_chart_compatibility :
    f.comp (verticalSecantAddition W) = g.comp (verticalTangentAddition W) := by
  let fs := f.comp (reciprocalTargetRestriction W _ (verticalSecantSlope W))
  let gs := g.comp (reciprocalTargetRestriction W _ (verticalTangentSlope W))
  have hb : fs.comp (ratioRestriction W (verticalSecantDenominator W)) =
      gs.comp (ratioRestriction W (tangentNumerator W)) := hbase
  have hm : fs (verticalSecantSlope W) = gs (verticalTangentSlope W) :=
    verticalSlope_chart_compatibility W f g hbase
  have hc (i) : fs (reciprocalCoordinates W (ratioRestriction W (verticalSecantDenominator W))
        (verticalSecantSlope W) i) =
      gs (reciprocalCoordinates W (ratioRestriction W (tangentNumerator W))
        (verticalTangentSlope W) i) := by
    rw [reciprocalCoordinates_map, reciprocalCoordinates_map, hb, hm]
  have hf := congrArg f (reciprocalTargetInverse_mul W
    (ratioRestriction W (verticalSecantDenominator W)) (verticalSecantSlope W))
  have hg := congrArg g (reciprocalTargetInverse_mul W
    (ratioRestriction W (tangentNumerator W)) (verticalTangentSlope W))
  simp only [map_mul, map_one] at hf hg
  change f (reciprocalTargetInverse W _ (verticalSecantSlope W)) *
    fs (reciprocalCoordinates W (ratioRestriction W (verticalSecantDenominator W))
        (verticalSecantSlope W) 1) = 1 at hf
  change g (reciprocalTargetInverse W _ (verticalTangentSlope W)) *
    gs (reciprocalCoordinates W (ratioRestriction W (tangentNumerator W))
        (verticalTangentSlope W) 1) = 1 at hg
  rw [hc] at hf
  have hi : f (reciprocalTargetInverse W _ (verticalSecantSlope W)) =
      g (reciprocalTargetInverse W _ (verticalTangentSlope W)) := by
    linear_combination g (reciprocalTargetInverse W _ (verticalTangentSlope W)) * hf -
      f (reciprocalTargetInverse W _ (verticalSecantSlope W)) * hg
  apply hom_ext
  intro i
  change f (verticalSecantAddition W (coord W 1 i)) =
    g (verticalTangentAddition W (coord W 1 i))
  simp only [verticalSecantAddition, verticalTangentAddition, reciprocalAddition_coord,
    map_mul, hi]
  exact congrArg (g (reciprocalTargetInverse W _ (verticalTangentSlope W)) * ·) (hc i)

end FLT.Mazur.WeierstrassIntegralChart
