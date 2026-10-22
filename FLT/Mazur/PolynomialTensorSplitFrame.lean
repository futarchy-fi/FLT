/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreePolynomialNorm
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Extending a complete algebra frame to polynomial scalars

An isomorphism of the whole scalar-extended source gives an isomorphism of
its polynomial extension. This construction preserves all coordinates and
does not replace the source by its reduction or by selected branches.
-/

@[expose] public noncomputable section
open Polynomial TensorProduct
namespace FLT.Mazur.PolynomialTensorSplitFrame
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B T I : Type*} [CommRing R] [CommRing B] [CommRing T]
  [Algebra R B] [Algebra R T] [Fintype I]
  (e : (T ⊗[R] B) ≃ₐ[T] (I → T))
attribute [local instance] Polynomial.algebra

/-- Each coordinate is an actual map from the unchanged source coefficient ring. -/
def coordinate (i : I) : B →+* T :=
  ((Pi.evalRingHom (fun _ : I ↦ T) i).comp e.toRingHom).comp
    Algebra.TensorProduct.includeRight.toRingHom

/-- The complete frame after both polynomial extension and scalar extension. -/
def polynomialFrame :
    (T[X] ⊗[R[X]] (R[X] ⊗[R] B)) ≃ₐ[T[X]] (I → T[X]) := by
  classical
  exact (Algebra.TensorProduct.cancelBaseChange R R[X] T[X] T[X] B).trans
    ((Algebra.TensorProduct.cancelBaseChange R T T[X] T[X] B).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : T[X] ≃ₐ[T[X]] T[X]) e).trans
        (Algebra.TensorProduct.piScalarRight T T[X] T[X] I)))

/-- The polynomial frame has the original coordinate maps on source coefficients. -/
theorem polynomialFrame_coefficient (b : B) (i : I) :
    polynomialFrame e (1 ⊗ₜ[R[X]] (1 ⊗ₜ[R] b)) i = C (coordinate e i b) := by
  classical
  simp [polynomialFrame, coordinate, Algebra.smul_def]

/-- Polynomial scalars retain their actual coordinatewise scalar action. -/
theorem polynomialFrame_scalar (P : R[X]) (i : I) :
    polynomialFrame e (1 ⊗ₜ[R[X]]
      (algebraMap R[X] (R[X] ⊗[R] B) P)) i = P.map (algebraMap R T) := by
  classical
  change polynomialFrame e (1 ⊗ₜ[R[X]] (P ⊗ₜ[R] 1)) i = _
  simp [polynomialFrame, Algebra.smul_def, Polynomial.algebraMap_def,
    ← Algebra.TensorProduct.one_def]

/-- Every coefficient of the chosen polynomial is evaluated along the same full-frame coordinate. -/
theorem polynomialFrame_element (P : B[X]) (i : I) :
    polynomialFrame e (1 ⊗ₜ[R[X]] (FiniteFreePolynomialNorm.element P)) i =
      P.map (coordinate e i) := by
  let φ : (R[X] ⊗[R] B) →+* T[X] :=
    ((Pi.evalRingHom (fun _ : I ↦ T[X]) i).comp (polynomialFrame e).toRingHom).comp
      Algebra.TensorProduct.includeRight.toRingHom
  change φ (P.eval₂ Algebra.TensorProduct.includeRight.toRingHom
    (algebraMap R[X] (R[X] ⊗[R] B) X)) = _
  rw [hom_eval₂]
  have hc : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      C.comp (coordinate e i) := by
    ext b : 1
    exact polynomialFrame_coefficient e b i
  have hx : φ (algebraMap R[X] (R[X] ⊗[R] B) X) = X := by
    exact (polynomialFrame_scalar e X i).trans (map_X _)
  rw [hc, hx, ← eval₂_map, eval₂_C_X]

end FLT.Mazur.PolynomialTensorSplitFrame
