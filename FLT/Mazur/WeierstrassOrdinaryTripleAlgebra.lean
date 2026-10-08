/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization
public import FLT.Mazur.WeierstrassOrdinaryTripleCoordinates

/-!
# Comparing the actual ordinary triple-output algebra maps

Compatible specializations of two ordinary inner charts and two secant outer
charts have equal output algebra maps. The compatibility hypotheses identify
only their inputs, never either iterated output.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The two actual outer output maps agree on every compatible common algebra. -/
theorem ordinaryTripleAlgebra (b c : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (ordinaryIndex c) →ₐ[R] S)
    (h k : additionChartRing W (ordinaryIndex false) →ₐ[R] S)
    (hmid : f.comp (ordinaryInputRight W b) = g.comp (ordinaryInputLeft W c))
    (hleft : h.comp (ordinaryInputLeft W false) = f.comp (ordinaryChartAddition W b))
    (hthird : h.comp (ordinaryInputRight W false) = g.comp (ordinaryInputRight W c))
    (hfirst : k.comp (ordinaryInputLeft W false) = f.comp (ordinaryInputLeft W b))
    (hright : k.comp (ordinaryInputRight W false) = g.comp (ordinaryChartAddition W c)) :
    h.comp (ordinaryChartAddition W false) = k.comp (ordinaryChartAddition W false) := by
  have hm (i) : g (ordinaryInputLeft W c (coord W 2 i)) =
      f (ordinaryInputRight W b (coord W 2 i)) :=
    (DFunLike.congr_fun hmid (coord W 2 i)).symm
  have hl (i) : h (ordinaryInputLeft W false (coord W 2 i)) =
      f (ordinaryChartAddition W b (coord W 2 i)) := DFunLike.congr_fun hleft _
  have ht (i) : h (ordinaryInputRight W false (coord W 2 i)) =
      g (ordinaryInputRight W c (coord W 2 i)) := DFunLike.congr_fun hthird _
  have hf (i) : k (ordinaryInputLeft W false (coord W 2 i)) =
      f (ordinaryInputLeft W b (coord W 2 i)) := DFunLike.congr_fun hfirst _
  have hr (i) : k (ordinaryInputRight W false (coord W 2 i)) =
      g (ordinaryChartAddition W c (coord W 2 i)) := DFunLike.congr_fun hright _
  have h₁ := ordinarySpecialization_line W b f
  have h₂ := ordinarySpecialization_line W c g
  have hc₁ := ordinarySpecialization_cubic W b f
  have hc₂ := ordinarySpecialization_cubic W c g
  dsimp only at hc₁ hc₂
  rw [hm 0, hm 1] at h₂ hc₂
  have hn := ordinarySpecialization_line W false h
  have ho := ordinarySpecialization_line W false k
  have hd := ordinarySpecialization_secant_unit W h
  have he := ordinarySpecialization_secant_unit W k
  simp only [hl, ht, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hn hd
  simp only [hf, hr, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one, hm] at ho he
  have heq := ordinary_triple_add_coordinates (W.map (algebraMap R S)).toAffine
    h₁ h₂ hc₁ hc₂ hn ho hd he
  apply hom_ext
  intro i
  change h (ordinaryChartAddition W false (coord W 2 i)) =
    k (ordinaryChartAddition W false (coord W 2 i))
  fin_cases i
  · change h (ordinaryChartAddition W false (coord W 2 0)) =
      k (ordinaryChartAddition W false (coord W 2 0))
    simpa only [ordinarySpecialization_coord, Matrix.cons_val_zero, Matrix.cons_val_one,
      hl, ht, hf, hr, hm] using heq.1
  · change h (ordinaryChartAddition W false (coord W 2 1)) =
      k (ordinaryChartAddition W false (coord W 2 1))
    simpa only [ordinarySpecialization_coord, Matrix.cons_val_zero, Matrix.cons_val_one,
      hl, ht, hf, hr, hm] using heq.2
  · change h (ordinaryChartAddition W false (coord W 2 2)) =
      k (ordinaryChartAddition W false (coord W 2 2))
    simp only [coord_self, map_one]

end FLT.Mazur.WeierstrassIntegralChart
