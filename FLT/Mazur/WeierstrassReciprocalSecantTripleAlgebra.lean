/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalChartSpecialization
public import FLT.Mazur.WeierstrassReciprocalSecantTriple

/-!
# Reciprocal secant triple-output algebra maps

Ordinary inner charts and reciprocal secant outer charts have equal actual
normalized outputs on every compatible common algebra, including infinity output.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassIntegralAddition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The two reciprocal outer secant maps agree on their compatible common algebra. -/
theorem reciprocalSecantTripleAlgebra (b c : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S)
    (g : additionChartRing W (ordinaryIndex c) →ₐ[R] S)
    (h : additionChartRing W (reciprocalIndex false) →ₐ[R] S)
    (k : additionChartRing W (reciprocalIndex false) →ₐ[R] S)
    (hmid : f.comp (ordinaryInputRight W b) = g.comp (ordinaryInputLeft W c))
    (hleft : h.comp (reciprocalInputLeft W false) = f.comp (ordinaryChartAddition W b))
    (hthird : h.comp (reciprocalInputRight W false) = g.comp (ordinaryInputRight W c))
    (hfirst : k.comp (reciprocalInputLeft W false) = f.comp (ordinaryInputLeft W b))
    (hright : k.comp (reciprocalInputRight W false) = g.comp (ordinaryChartAddition W c)) :
    h.comp (reciprocalChartAddition W false) = k.comp (reciprocalChartAddition W false) := by
  have hm (i) : g (ordinaryInputLeft W c (coord W 2 i)) =
      f (ordinaryInputRight W b (coord W 2 i)) :=
    (DFunLike.congr_fun hmid (coord W 2 i)).symm
  have hl (i) : h (reciprocalInputLeft W false (coord W 2 i)) =
      f (ordinaryChartAddition W b (coord W 2 i)) := DFunLike.congr_fun hleft _
  have ht (i) : h (reciprocalInputRight W false (coord W 2 i)) =
      g (ordinaryInputRight W c (coord W 2 i)) := DFunLike.congr_fun hthird _
  have hf (i) : k (reciprocalInputLeft W false (coord W 2 i)) =
      f (ordinaryInputLeft W b (coord W 2 i)) := DFunLike.congr_fun hfirst _
  have hr (i) : k (reciprocalInputRight W false (coord W 2 i)) =
      g (ordinaryChartAddition W c (coord W 2 i)) := DFunLike.congr_fun hright _
  have h₁ := ordinarySpecialization_line W b f
  have h₂ := ordinarySpecialization_line W c g
  have hc₁ := ordinarySpecialization_cubic W b f
  have hc₂ := ordinarySpecialization_cubic W c g
  dsimp only at hc₁ hc₂
  rw [hm 0, hm 1] at h₂ hc₂
  have hn := reciprocalSpecialization_line W false h
  have ho := reciprocalSpecialization_line W false k
  have hd := reciprocalSpecialization_secant_unit W h
  have he := reciprocalSpecialization_secant_unit W k
  simp only [hl, ht, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hn hd
  simp only [hf, hr, ordinarySpecialization_coord, Matrix.cons_val_zero,
    Matrix.cons_val_one, hm] at ho he
  have heq := (reciprocal_secant_triple_coordinates (W.map (algebraMap R S))
    h₁ h₂ hc₁ hc₂ hn ho hd he).2
  let t := (1 + (f (ordinaryChartSlope W b) - g (ordinaryChartSlope W c)) *
    h (reciprocalChartSlope W false)) ^ 3
  let A := h (reciprocalChartInverse W false)
  let B := k (reciprocalChartInverse W false)
  let L := reciprocalXYZ (W.map (algebraMap R S))
    (h (reciprocalInputLeft W false (coord W 2 0)))
    (h (reciprocalInputRight W false (coord W 2 0)))
    (h (reciprocalInputLeft W false (coord W 2 1)))
    (h (reciprocalChartSlope W false))
  let M := reciprocalXYZ (W.map (algebraMap R S))
    (k (reciprocalInputLeft W false (coord W 2 0)))
    (k (reciprocalInputRight W false (coord W 2 0)))
    (k (reciprocalInputLeft W false (coord W 2 1)))
    (k (reciprocalChartSlope W false))
  have hscale (i : Fin 3) : L i = t * M i := by
    dsimp only [L, M, t]
    simpa only [hl, ht, hf, hr, hm, ordinarySpecialization_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one] using heq i
  have hA : A * L 1 = 1 := by
    rw [← reciprocalSpecialization_coord W false h 1, coord_self, map_one, map_one]
  have hB : B * M 1 = 1 := by
    rw [← reciprocalSpecialization_coord W false k 1, coord_self, map_one, map_one]
  have hnorm : A * t = B := by
    calc
      A * t = (A * t) * (B * M 1) := by rw [hB, mul_one]
      _ = B * (A * L 1) := by rw [hscale 1]; ring
      _ = B := by rw [hA, mul_one]
  apply hom_ext
  intro i
  change h (reciprocalChartAddition W false (coord W 1 i)) =
    k (reciprocalChartAddition W false (coord W 1 i))
  rw [reciprocalSpecialization_coord, reciprocalSpecialization_coord]
  change A * L i = B * M i
  rw [hscale, ← mul_assoc, hnorm]

end FLT.Mazur.WeierstrassIntegralChart
