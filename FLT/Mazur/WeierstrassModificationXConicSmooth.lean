/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicSecondOpen
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smoothness of the original conic

Both original tangent neighborhoods are parameter opens of the affine line.
They cover when a is a unit, so target-locality proves smoothness of the
actual conic algebra over the coefficient ring, with arbitrary c.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)

/-- The parameter open is a smooth algebra over the coefficient ring. -/
theorem conicParameterOpen_smooth : Algebra.Smooth R (ConicParameterOpen c) := by
  let _ : Algebra.Smooth R R[X] := { }
  let _ : Algebra.Smooth R[X] (ConicParameterOpen c) :=
    Algebra.Smooth.of_isLocalization_Away (conicParameterPolynomial c)
  exact Algebra.Smooth.comp R R[X] (ConicParameterOpen c)

/-- The actual first tangent neighborhood is smooth. -/
theorem conicFirstOpen_smooth (ha : IsUnit a) : Algebra.Smooth R (ConicFirstOpen a c) := by
  let _ := conicParameterOpen_smooth c
  exact Algebra.Smooth.of_equiv (conicFirstParameterEquiv a c ha)

/-- The actual second tangent neighborhood is smooth. -/
theorem conicSecondOpen_smooth (ha : IsUnit a) : Algebra.Smooth R (ConicSecondOpen a c) := by
  let _ := conicParameterOpen_smooth c
  exact Algebra.Smooth.of_equiv (conicSecondParameterEquiv a c ha)

/-- The two tangent denominators generate the unit ideal in the original conic. -/
theorem conic_tangent_span (ha : IsUnit a) :
    Ideal.span ({conicV a c + algebraMap R (ConicCoordinate a c) a, conicV a c} :
      Set (ConicCoordinate a c)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ _ (ha.map (algebraMap R (ConicCoordinate a c)))
  have hu : conicV a c + algebraMap R (ConicCoordinate a c) a ∈
      Ideal.span ({conicV a c + algebraMap R (ConicCoordinate a c) a, conicV a c} :
        Set (ConicCoordinate a c)) := Ideal.subset_span (by simp)
  have hv : conicV a c ∈
      Ideal.span ({conicV a c + algebraMap R (ConicCoordinate a c) a, conicV a c} :
        Set (ConicCoordinate a c)) := Ideal.subset_span (by simp)
  simpa only [add_sub_cancel_left] using Ideal.sub_mem _ hu hv

/-- The full conic, not just its tangent neighborhoods, is smooth over R. -/
theorem conicCoordinate_smooth (ha : IsUnit a) : Algebra.Smooth R (ConicCoordinate a c) := by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.ofLocalizationSpanTarget _
    {conicV a c + algebraMap R (ConicCoordinate a c) a, conicV a c}
    (conic_tangent_span a c ha)
  rintro ⟨r, hr⟩
  rcases Set.mem_insert_iff.mp hr with h | h
  · subst r
    rw [← IsScalarTower.algebraMap_eq R (ConicCoordinate a c) (ConicFirstOpen a c)]
    exact RingHom.smooth_algebraMap.mpr (conicFirstOpen_smooth a c ha)
  · have h := Set.mem_singleton_iff.mp h
    subst r
    rw [← IsScalarTower.algebraMap_eq R (ConicCoordinate a c) (ConicSecondOpen a c)]
    exact RingHom.smooth_algebraMap.mpr (conicSecondOpen_smooth a c ha)

end FLT.Mazur.WeierstrassModificationX
