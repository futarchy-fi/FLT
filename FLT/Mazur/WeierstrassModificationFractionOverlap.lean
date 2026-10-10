/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationLifting
public import FLT.Mazur.WeierstrassDilatationFractionMap
public import FLT.Mazur.WeierstrassModificationXContractionOverlap
public import FLT.Mazur.WeierstrassModificationXFractionMap
public import FLT.Mazur.WeierstrassModificationYContractionOverlap
public import FLT.Mazur.WeierstrassModificationYFractionMap

/-!
# The existing substitutions agree with original fraction transitions

On an algebra where the relevant original denominators are invertible, the
proved overlap substitutions give exactly the maps from original fractions.
The equality is on every chart function and preserves the original cubic map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationFractionOverlap

set_option backward.isDefEq.respectTransparency false

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] S)

local notation "D" => WeierstrassDilatation.fractionMap W s b3 b4 b6 h3 h4 h6
local notation "X" => WeierstrassModificationX.fractionMap W s b3 b4 b6 h3 h4 h6
local notation "Y" => WeierstrassModificationY.fractionMap W s b3 b4 b6 h3 h4 h6

/-- The y-to-x substitution is the original x-fraction map on the common original open. -/
theorem y_to_x (dy dx : S)
    (hy : f (WeierstrassIntegralChart.coord W 2 1) * dy = 1)
    (hx : f (WeierstrassIntegralChart.coord W 2 0) * dx = 1)
    (a : Sˣ) (ha : Y f dy hy (WeierstrassModificationY.coord W s b3 b4 b6 1) = a) :
    WeierstrassModificationY.toX W s b3 b4 b6 (Y f dy hy) a ha = X f dx hx := by
  symm
  apply WeierstrassModificationX.lift_unique W s b3 b4 b6 h3 h4 h6
  · rw [WeierstrassModificationX.fractionMap_x]
    exact (isUnit_iff_exists_inv.mpr ⟨dx, hx⟩).isRegular
  · rw [WeierstrassModificationX.fractionMap_fromOriginal,
      WeierstrassModificationY.toX_fromOriginal,
      WeierstrassModificationY.fractionMap_fromOriginal]

/-- The y-to-divided substitution is the original scale-fraction map. -/
theorem y_to_divided (dy ds : S)
    (hy : f (WeierstrassIntegralChart.coord W 2 1) * dy = 1)
    (hs : algebraMap R S s * ds = 1)
    (a : Sˣ) (ha : Y f dy hy (WeierstrassModificationY.coord W s b3 b4 b6 0) = a) :
    WeierstrassModificationY.toDivided W s b3 b4 b6 (Y f dy hy) a ha = D f ds hs := by
  apply WeierstrassDilatation.lift_unique W s b3 b4 b6 h3 h4 h6
    (isUnit_iff_exists_inv.mpr ⟨ds, hs⟩).isRegular
  rw [WeierstrassModificationY.toDivided_fromOriginal,
    WeierstrassModificationY.fractionMap_fromOriginal,
    WeierstrassDilatation.fractionMap_fromOriginal]

/-- The x-to-divided substitution is the original scale-fraction map. -/
theorem x_to_divided (dx ds : S)
    (hx : f (WeierstrassIntegralChart.coord W 2 0) * dx = 1)
    (hs : algebraMap R S s * ds = 1)
    (a : Sˣ) (ha : X f dx hx (WeierstrassModificationX.t W s b3 b4 b6) = a) :
    WeierstrassModificationX.dividedOverlapMap W s b3 b4 b6 (X f dx hx) a ha =
      D f ds hs := by
  apply WeierstrassDilatation.lift_unique W s b3 b4 b6 h3 h4 h6
    (isUnit_iff_exists_inv.mpr ⟨ds, hs⟩).isRegular
  rw [WeierstrassModificationX.dividedOverlapMap_fromOriginal,
    WeierstrassModificationX.fractionMap_fromOriginal,
    WeierstrassDilatation.fractionMap_fromOriginal]

end FLT.Mazur.WeierstrassModificationFractionOverlap
