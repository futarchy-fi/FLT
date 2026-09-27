/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistCoassociativity

/-!
# Geometric points of a quadratic twist

A chosen embedding of the quadratic coefficients identifies points of the
fixed model with points of the original algebra. Changing that embedding by
conjugation acts through the twisting involution.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R H Ω : Type v} [CommRing R] [CommRing H] [CommRing Ω]
variable [Algebra R H] [Algebra R Ω]
variable (u : Rˣ) (ι : H ≃ₐ[R] H)

/-- Restrict a point, evaluated at chosen quadratic coefficients, to the fixed model. -/
noncomputable def pointMap (s : QuadraticAlgebra R (u : R) 0 →ₐ[R] Ω)
    (f : H →ₐ[R] Ω) : model (u : R) ι →ₐ[R] Ω :=
  (Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _)).comp (model (u : R) ι).val

/-- Evaluation on the fixed model is unchanged when both factors are conjugated. -/
theorem pointMap_conjugation (s : QuadraticAlgebra R (u : R) 0 →ₐ[R] Ω)
    (f : H →ₐ[R] Ω) :
    pointMap u ι (s.comp (conjugation (u : R)).toAlgHom) (f.comp ι.toAlgHom) =
      pointMap u ι s f := by
  apply AlgHom.ext
  intro a
  have he (z : QuadraticAlgebra R (u : R) 0 ⊗[R] H) :
      Algebra.TensorProduct.lift (s.comp (conjugation (u : R)).toAlgHom)
        (f.comp ι.toAlgHom) (fun _ _ ↦ .all _ _) z =
      Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _) (involution (u : R) ι z) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t h => rfl
  exact (he a.val).trans (congrArg (Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _))
    a.property)

/-- Postcomposition of a descended point acts on its coefficients and original point. -/
theorem pointMap_postcomp (s : QuadraticAlgebra R (u : R) 0 →ₐ[R] Ω)
    (f : H →ₐ[R] Ω) (σ : Ω →ₐ[R] Ω) :
    σ.comp (pointMap u ι s f) = pointMap u ι (σ.comp s) (σ.comp f) := by
  apply AlgHom.ext
  intro a
  have he (z : QuadraticAlgebra R (u : R) 0 ⊗[R] H) :
      σ (Algebra.TensorProduct.lift s f (fun _ _ ↦ .all _ _) z) =
      Algebra.TensorProduct.lift (σ.comp s) (σ.comp f) (fun _ _ ↦ .all _ _) z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t h => exact map_mul σ _ _
  exact he a.val

/-- Automorphisms fixing the chosen quadratic coefficients act on the original points. -/
theorem pointMap_postcomp_of_fixed (s : QuadraticAlgebra R (u : R) 0 →ₐ[R] Ω)
    (f : H →ₐ[R] Ω) (σ : Ω →ₐ[R] Ω) (hσ : σ.comp s = s) :
    σ.comp (pointMap u ι s f) = pointMap u ι s (σ.comp f) := by
  rw [pointMap_postcomp, hσ]

/-- Automorphisms conjugating the coefficients act on points through the twisting involution. -/
theorem pointMap_postcomp_of_conjugation (hι : Function.Involutive ι)
    (s : QuadraticAlgebra R (u : R) 0 →ₐ[R] Ω)
    (f : H →ₐ[R] Ω) (σ : Ω →ₐ[R] Ω)
    (hσ : σ.comp s = s.comp (conjugation (u : R)).toAlgHom) :
    σ.comp (pointMap u ι s f) = pointMap u ι s ((σ.comp f).comp ι.toAlgHom) := by
  rw [pointMap_postcomp, hσ]
  have hh : ((σ.comp f).comp ι.toAlgHom).comp ι.toAlgHom = σ.comp f := by
    ext x
    exact congrArg (σ.comp f) (hι x)
  rw [← pointMap_conjugation u ι s ((σ.comp f).comp ι.toAlgHom), hh]

variable (hι : Function.Involutive ι) (r : R) (hr : 2 * r = 1)
variable [Algebra (QuadraticAlgebra R (u : R) 0) Ω]
variable [IsScalarTower R (QuadraticAlgebra R (u : R) 0) Ω]

/-- Scalar recovery identifies the geometric points after choosing quadratic coefficients. -/
noncomputable def pointsEquiv :
    (H →ₐ[R] Ω) ≃ (model (u : R) ι →ₐ[R] Ω) :=
  (Algebra.TensorProduct.liftEquivRight R (QuadraticAlgebra R (u : R) 0) H Ω).trans
    ((AlgEquiv.arrowCongr (scalarExtensionEquivOver u ι hι r hr).symm AlgEquiv.refl).trans
      (Algebra.TensorProduct.liftEquivRight R (QuadraticAlgebra R (u : R) 0)
        (model (u : R) ι) Ω).symm)

/-- The geometric-point equivalence is restriction of coefficient evaluation. -/
theorem pointsEquiv_apply (f : H →ₐ[R] Ω) :
    pointsEquiv u ι hι r hr f =
      pointMap u ι (IsScalarTower.toAlgHom R (QuadraticAlgebra R (u : R) 0) Ω) f := by
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.lift (Algebra.ofId (QuadraticAlgebra R (u : R) 0) Ω) f
    (fun _ _ ↦ .all _ _)
    (scalarExtensionEquiv u ι hι r hr (1 ⊗ₜ[R] a)) = _
  rw [scalarExtensionEquiv_tmul]
  simp only [← Algebra.TensorProduct.one_def, one_mul]
  rfl

end QuadraticTwist
