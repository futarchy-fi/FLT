/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartOverlap
public import FLT.Mazur.WeierstrassDilatationReesChart

/-!
# The modification center on every original projective chart

The ideals (s,X,Y) agree under the original unit coordinate transitions.
On the X and Y charts they are the unit ideal; on the affine Z chart they
are precisely the original modification center, with its full scheme structure.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s : R)

/-- The original homogeneous center expressed in a normalized projective chart. -/
def modificationChartCenter (j : Fin 3) : Ideal (Coordinate W j) :=
  Ideal.span {algebraMap R _ s, coord W j 0, coord W j 1}

/-- Its affine member is the original Rees modification center. -/
theorem modificationChartCenter_affine :
    modificationChartCenter W s 2 = WeierstrassDilatation.modificationCenter W s := rfl

/-- Specializing a center retains its three actual generators. -/
theorem modificationChartCenter_map (j : Fin 3) (f : Coordinate W j →ₐ[R] S) :
    (modificationChartCenter W s j).map f.toRingHom =
      Ideal.span {algebraMap R S s, f (coord W j 0), f (coord W j 1)} := by
  simp only [modificationChartCenter, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

/-- The infinity and redundant X charts do not meet the center as schemes. -/
theorem modificationChartCenter_eq_top (j : Fin 3) (hj : j = 0 ∨ j = 1) :
    modificationChartCenter W s j = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rcases hj with rfl | rfl
  · exact Ideal.subset_span (by simp [coord_self])
  · exact Ideal.subset_span (by simp [coord_self])

/-- The full center ideal agrees on each original projective coordinate overlap. -/
theorem modificationChartCenter_overlap (j k : Fin 3) :
    (modificationChartCenter W s k).map (transitionBase W j k).toRingHom =
      (modificationChartCenter W s j).map (algebraMap (Coordinate W j) (Overlap W j k)) := by
  rw [modificationChartCenter_map]
  change _ = (modificationChartCenter W s j).map
    (IsScalarTower.toAlgHom R (Coordinate W j) (Overlap W j k)).toRingHom
  rw [modificationChartCenter_map]
  simp only [transitionBase_coord, Ideal.span_insert,
    Ideal.span_singleton_mul_left_unit (overlapInverse_isUnit W j k)]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
