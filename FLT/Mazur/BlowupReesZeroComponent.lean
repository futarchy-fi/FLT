/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesRatio

/-!
# The original coefficient ring is the degree-zero Rees component

The comparison is a ring isomorphism, and the homogeneous localization
maps retain every original coefficient under the fraction-chart comparison.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- Original constants as actual degree-zero elements of the Rees algebra. -/
def originalToZero : A →+* component I 0 where
  toFun a := ⟨algebraMap A (reesAlgebra I) a, ⟨⟨a, by simp⟩, by
    apply Subtype.ext
    change Polynomial.monomial 0 a = Polynomial.C a
    simp only [Polynomial.monomial_zero_left]⟩⟩
  map_one' := Subtype.ext (map_one (algebraMap A (reesAlgebra I)))
  map_mul' a b := Subtype.ext (map_mul (algebraMap A (reesAlgebra I)) a b)
  map_zero' := Subtype.ext (map_zero (algebraMap A (reesAlgebra I)))
  map_add' a b := Subtype.ext (map_add (algebraMap A (reesAlgebra I)) a b)

/-- Extracting the constant coefficient recovers the original constant. -/
theorem originalToZero_coeff (a : A) :
    (((originalToZero I a : component I 0) : reesAlgebra I) : A[X]).coeff 0 = a := by
  change (Polynomial.C a).coeff 0 = a
  exact Polynomial.coeff_C_zero

/-- Every degree-zero Rees element is a unique original constant. -/
theorem originalToZero_bijective : Function.Bijective (originalToZero I) := by
  constructor
  · intro a b h
    have hc := congrArg (fun z : component I 0 => ((z : reesAlgebra I) : A[X]).coeff 0) h
    simpa only [originalToZero_coeff] using hc
  · intro p
    refine ⟨((p : reesAlgebra I) : A[X]).coeff 0, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change Polynomial.C (((p : reesAlgebra I) : A[X]).coeff 0) = _
    exact Polynomial.monomial_zero_left.symm.trans
      (component_eq_monomial I 0 p p.property).symm

/-- The original coordinate ring is precisely the degree-zero Rees component. -/
def originalZeroEquiv : A ≃+* component I 0 :=
  RingEquiv.ofBijective (originalToZero I) (originalToZero_bijective I)

variable (f : A) (hf : f ∈ I)

/-- Original constants in a degree-zero homogeneous chart are degree-zero fractions. -/
theorem fromZero_original (a : A) :
    HomogeneousLocalization.fromZeroRingHom (component I) _ (originalToZero I a) =
      homogeneousFraction I f hf 0 ⟨a, by simp⟩ := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (algebraMap A (reesAlgebra I) a) 1 = _
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk]
  congr 1

/-- The degree-zero comparison retains the original coordinate algebra map. -/
@[simp] theorem degreeZeroEquiv_original (a : A) :
    degreeZeroEquiv I f hf
        (HomogeneousLocalization.fromZeroRingHom (component I) _ (originalToZero I a)) =
      algebraMap A (BlowupFractionChart.chart I f) a := by
  rw [fromZero_original]
  apply Subtype.ext
  rw [degreeZeroEquiv_fraction]
  simp only [pow_zero, mul_one]
  rfl

end FLT.Mazur.BlowupRees
