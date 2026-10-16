/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCoefficients

/-!
# Arbitrary coefficient maps on the original initial equation

The map preserves the original incidence and slope generators. Constants and
these two functions determine every ring map out of the full initial algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Constants, incidence and slope determine every ring map on the original initial equation. -/
theorem coefficient_ringHom_ext (W : WeierstrassCurve R) (s b3 b4 b6 : R)
    (g h : Coordinate W s b3 b4 b6 →+* S)
    (hc : ∀ a, g (algebraMap R _ a) = h (algebraMap R _ a))
    (ht : g (t W s b3 b4 b6) = h (t W s b3 b4 b6))
    (hv : g (v W s b3 b4 b6) = h (v W s b3 b4 b6)) : g = h := by
  let _ := (g.comp (algebraMap R (Coordinate W s b3 b4 b6))).toAlgebra
  let g' : Coordinate W s b3 b4 b6 →ₐ[R] S := ⟨g, fun _ ↦ rfl⟩
  let h' : Coordinate W s b3 b4 b6 →ₐ[R] S := ⟨h, fun a ↦ (hc a).symm⟩
  exact congrArg AlgHom.toRingHom (hom_ext W s b3 b4 b6 g' h' ht hv)

variable (f : R →+* S) (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Change the coefficients of the full original initial equation. -/
def coefficientRingMap : Coordinate W s b3 b4 b6 →+*
    Coordinate (W.map f) (f s) (f b3) (f b4) (f b6) :=
  let _ := f.toAlgebra
  (coefficientMap W s b3 b4 b6 S).toRingHom

/-- The actual original coefficient action on every scalar. -/
theorem coefficientRingMap_scalar (a : R) :
    coefficientRingMap f W s b3 b4 b6 (algebraMap R _ a) = algebraMap S _ (f a) := by
  let _ := f.toAlgebra
  exact (coefficientMap W s b3 b4 b6 S).commutes a

/-- The original incidence generator is preserved at all points. -/
theorem coefficientRingMap_t :
    coefficientRingMap f W s b3 b4 b6 (t W s b3 b4 b6) =
      t (W.map f) (f s) (f b3) (f b4) (f b6) := by
  let _ := f.toAlgebra
  exact coefficientMap_t W s b3 b4 b6 S

/-- The entire slope generator is preserved. -/
theorem coefficientRingMap_v :
    coefficientRingMap f W s b3 b4 b6 (v W s b3 b4 b6) =
      v (W.map f) (f s) (f b3) (f b4) (f b6) := by
  let _ := f.toAlgebra
  exact coefficientMap_v W s b3 b4 b6 S

end FLT.Mazur.WeierstrassModificationX
