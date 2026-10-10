/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityChartSpecialization

/-!
# Exact homogeneous criteria for equality of infinity outputs

Only the constructed output Y units are canceled. Two homogeneous minors
therefore characterize equality of the actual normalized chart maps over
every coefficient algebra, including nonreduced rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f g : InfinityAdditionOpen W →ₐ[R] S)

/-- A normalized coordinate agrees exactly when its homogeneous minor vanishes. -/
theorem infinitySpecialization_coord_eq_iff (i : Fin 3) :
    f (infinityAdditionChart W (coord W 1 i)) =
        g (infinityAdditionChart W (coord W 1 i)) ↔
      f (infinityOutputRestriction W (infinityOutputCoordinates W i)) *
          g (infinityOutputRestriction W (infinityOutputCoordinates W 1)) =
        g (infinityOutputRestriction W (infinityOutputCoordinates W i)) *
          f (infinityOutputRestriction W (infinityOutputCoordinates W 1)) := by
  have hf := congrArg f (infinityAdditionChart_mul W i)
  have hg := congrArg g (infinityAdditionChart_mul W i)
  simp only [map_mul] at hf hg
  constructor
  · intro h
    rw [← hf, ← hg, h]
    ring
  · intro h
    apply (((infinityOutputY_isUnit W).map f).mul
      ((infinityOutputY_isUnit W).map g)).mul_left_inj.mp
    linear_combination
      g (infinityOutputRestriction W (infinityOutputCoordinates W 1)) * hf -
      f (infinityOutputRestriction W (infinityOutputCoordinates W 1)) * hg + h

/-- The two nonconstant coordinates detect equality of normalized infinity output maps. -/
theorem infinitySpecialization_output_eq_iff :
    f.comp (infinityAdditionChart W) = g.comp (infinityAdditionChart W) ↔
      f (infinityAdditionChart W (coord W 1 0)) =
          g (infinityAdditionChart W (coord W 1 0)) ∧
        f (infinityAdditionChart W (coord W 1 2)) =
          g (infinityAdditionChart W (coord W 1 2)) := by
  constructor
  · intro h
    exact ⟨DFunLike.congr_fun h _, DFunLike.congr_fun h _⟩
  · intro h
    apply hom_ext
    intro i
    fin_cases i
    · exact h.1
    · change (f.comp (infinityAdditionChart W)) (coord W 1 1) =
        (g.comp (infinityAdditionChart W)) (coord W 1 1)
      simp only [coord_self, map_one]
    · exact h.2

/-- Equality of both homogeneous minors is precisely equality of the genuine output maps. -/
theorem infinitySpecialization_output_eq_iff_minors :
    f.comp (infinityAdditionChart W) = g.comp (infinityAdditionChart W) ↔
      (∀ i ∈ ({0, 2} : Finset (Fin 3)),
        f (infinityOutputRestriction W (infinityOutputCoordinates W i)) *
            g (infinityOutputRestriction W (infinityOutputCoordinates W 1)) =
          g (infinityOutputRestriction W (infinityOutputCoordinates W i)) *
            f (infinityOutputRestriction W (infinityOutputCoordinates W 1))) := by
  rw [infinitySpecialization_output_eq_iff,
    infinitySpecialization_coord_eq_iff W f g 0,
    infinitySpecialization_coord_eq_iff W f g 2]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

end FLT.Mazur.WeierstrassIntegralChart
