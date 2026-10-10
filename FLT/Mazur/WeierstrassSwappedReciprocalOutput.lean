/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedSlopeComparison
public import FLT.Mazur.WeierstrassAffinePolynomialScaling

/-!
# Reciprocal outputs on reversed affine inputs

The homogeneous outputs agree before normalization. Their normalizing inverses
therefore agree too, giving equality of the actual infinity-chart output maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b c : Bool)
  (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
  (g : additionChartRing W (reciprocalIndex c) →ₐ[R] S)
  (hbase : g.comp (additionChartAlgRestriction W (reciprocalIndex c)) =
    (f.comp (additionChartAlgRestriction W (reciprocalIndex b))).comp (affineProductSwap W))

include hbase

/-- Homogeneous reciprocal coordinates agree on reversed inputs. -/
theorem reciprocalChartCoordinates_swap (i : Fin 3) :
    f (reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex b))
      (reciprocalChartSlope W b) i) =
    g (reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex c))
      (reciprocalChartSlope W c) i) := by
  have hb (a) := DFunLike.congr_fun hbase a
  have hs := reciprocalChartSlopes_swap W b c f g hbase
  have hl := congrArg f (reciprocalChartSlope_line W b)
  simp only [map_mul, secantDenominator, verticalSecantDenominator, map_sub] at hl
  rw [reciprocalCoordinates_map, reciprocalCoordinates_map]
  dsimp only [reciprocalCoordinates, AlgHom.comp_apply]
  simp only [AlgHom.comp_apply] at hb
  simp only [hb, affineProductSwap_x₁, affineProductSwap_x₂, affineProductSwap_y₁, ← hs]
  exact (congrFun (reciprocalAdditionXYZ_swap (W.map (algebraMap R S)) hl) i).symm

/-- The normalizing inverse is unchanged by reversing the two affine inputs. -/
theorem reciprocalChartInverse_swap :
    f (reciprocalChartInverse W b) = g (reciprocalChartInverse W c) := by
  have hf := congrArg f (reciprocalChartInverse_mul_coordinates W b)
  have hg := congrArg g (reciprocalChartInverse_mul_coordinates W c)
  simp only [map_mul, map_one] at hf hg
  rw [← reciprocalChartCoordinates_swap W b c f g hbase 1] at hg
  calc
    f (reciprocalChartInverse W b) =
        f (reciprocalChartInverse W b) *
          (g (reciprocalChartInverse W c) *
            f (reciprocalCoordinates W (additionChartAlgRestriction W (reciprocalIndex b))
              (reciprocalChartSlope W b) 1)) := by rw [hg, mul_one]
    _ = g (reciprocalChartInverse W c) := by
      rw [mul_left_comm, hf, mul_one]

/-- The actual normalized reciprocal addition maps agree on reversed inputs. -/
theorem reciprocalChartAddition_swap :
    f.comp (reciprocalChartAddition W b) = g.comp (reciprocalChartAddition W c) := by
  apply hom_ext
  intro i
  change f (reciprocalChartAddition W b (coord W 1 i)) =
    g (reciprocalChartAddition W c (coord W 1 i))
  rw [reciprocalChartAddition_coord, reciprocalChartAddition_coord, map_mul, map_mul,
    reciprocalChartInverse_swap W b c f g hbase,
    reciprocalChartCoordinates_swap W b c f g hbase]

end FLT.Mazur.WeierstrassIntegralChart
