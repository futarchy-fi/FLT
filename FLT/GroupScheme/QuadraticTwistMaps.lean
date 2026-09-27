/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwist

/-!
# Maps on the integral quadratic twist

Equivariant algebra maps descend to the fixed models. In particular the
counit and antipode descend for twisting by group inversion. These are
structure maps; the coalgebra and Hopf laws still require comultiplication.
-/

@[expose] public section

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R H J : Type v} [CommRing R] [CommRing H] [CommRing J]
variable [Algebra R H] [Algebra R J]
variable (d : R) (ι : H ≃ₐ[R] H) (κ : J ≃ₐ[R] J)

/-- Scalar extension of an equivariant algebra map intertwines the tensor involutions. -/
theorem baseChangeMap_equivariant (f : H →ₐ[R] J) (hf : ∀ x, κ (f x) = f (ι x))
    (z : QuadraticAlgebra R d 0 ⊗[R] H) :
    involution d κ (Algebra.TensorProduct.map (AlgHom.id R _) f z) =
      Algebra.TensorProduct.map (AlgHom.id R _) f (involution d ι z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change conjugation d s ⊗ₜ[R] κ (f x) = conjugation d s ⊗ₜ[R] f (ι x)
    rw [hf]

/-- An equivariant map induces an algebra map between integral quadratic twists. -/
def map (f : H →ₐ[R] J) (hf : ∀ x, κ (f x) = f (ι x)) :
    model d ι →ₐ[R] model d κ :=
  QuadraticDescent.fixedMap (involution d ι) (involution d κ)
    (Algebra.TensorProduct.map (AlgHom.id R _) f) (baseChangeMap_equivariant d ι κ f hf)

/-- Descent of a map agrees with its scalar extension on underlying elements. -/
@[simp] theorem map_apply (f : H →ₐ[R] J) (hf : ∀ x, κ (f x) = f (ι x))
    (z : model d ι) :
    (map d ι κ f hf z : QuadraticAlgebra R d 0 ⊗[R] J) =
      Algebra.TensorProduct.map (AlgHom.id R _) f z := rfl

/-- The original involution itself descends to the fixed twist model. -/
def modelInvolution : model d ι →ₐ[R] model d ι :=
  map d ι ι ι.toAlgHom (fun _ ↦ rfl)

/-- The descended involution still squares to the identity. -/
theorem modelInvolution_involutive (hι : Function.Involutive ι) :
    Function.Involutive (modelInvolution d ι) := by
  intro z
  apply Subtype.ext
  change Algebra.TensorProduct.map (AlgHom.id R _) ι.toAlgHom
    (Algebra.TensorProduct.map (AlgHom.id R _) ι.toAlgHom z.val) = z.val
  induction z.val using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x => change s ⊗ₜ[R] ι (ι x) = s ⊗ₜ[R] x; rw [hι]

/-- Scalar extension of an invariant augmentation takes values in the quadratic coefficients. -/
def coefficientCounit (ε : H →ₐ[R] R) :
    QuadraticAlgebra R d 0 ⊗[R] H →ₐ[R] QuadraticAlgebra R d 0 :=
  Algebra.TensorProduct.lift (AlgHom.id R _) ((Algebra.ofId R _).comp ε)
    (fun _ _ ↦ .all _ _)

/-- The extended augmentation respects coefficient conjugation. -/
theorem coefficientCounit_equivariant (ε : H →ₐ[R] R) (hε : ∀ x, ε (ι x) = ε x)
    (z : QuadraticAlgebra R d 0 ⊗[R] H) :
    conjugation d (coefficientCounit d ε z) =
      coefficientCounit d ε (involution d ι z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change conjugation d (s * algebraMap R _ (ε x)) =
      conjugation d s * algebraMap R _ (ε (ι x))
    rw [map_mul, AlgEquiv.commutes, hε]

/-- An invariant augmentation descends to the original coefficient ring. -/
noncomputable def modelCounit (ε : H →ₐ[R] R) (hε : ∀ x, ε (ι x) = ε x)
    (r : R) (hr : 2 * r = 1) : model d ι →ₐ[R] R :=
  (fixedScalarsEquiv d r hr).toAlgHom.comp
    (QuadraticDescent.fixedMap (involution d ι) (conjugation d)
      (coefficientCounit d ε) (coefficientCounit_equivariant d ι ε hε))

/-- The descended augmentation recovers the extended augmentation after coefficient inclusion. -/
theorem algebraMap_modelCounit (ε : H →ₐ[R] R) (hε : ∀ x, ε (ι x) = ε x)
    (r : R) (hr : 2 * r = 1) (z : model d ι) :
    algebraMap R (QuadraticAlgebra R d 0) (modelCounit d ι ε hε r hr z) =
      coefficientCounit d ε z := by
  let a := QuadraticDescent.fixedMap (involution d ι) (conjugation d)
    (coefficientCounit d ε) (coefficientCounit_equivariant d ι ε hε) z
  exact congrArg Subtype.val ((fixedScalarsEquiv d r hr).symm_apply_apply a)

end QuadraticTwist

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable (d : R)

/-- The descended antipode for the twist by group inversion. -/
noncomputable def antipode :
    model d (HopfAlgebra.antipodeAlgEquiv R H) →ₐ[R]
      model d (HopfAlgebra.antipodeAlgEquiv R H) :=
  modelInvolution d (HopfAlgebra.antipodeAlgEquiv R H)

/-- The descended antipode is involutive. -/
theorem antipode_involutive : Function.Involutive (antipode (H := H) d) :=
  modelInvolution_involutive d _ (HopfAlgebra.antipode_involutive R H)

/-- The descended counit for the twist by group inversion. -/
noncomputable def counit (r : R) (hr : 2 * r = 1) :
    model d (HopfAlgebra.antipodeAlgEquiv R H) →ₐ[R] R :=
  modelCounit d (HopfAlgebra.antipodeAlgEquiv R H) (Bialgebra.counitAlgHom R H)
    (fun x ↦ AlgHom.congr_fun (AlgHom.counitAlgHom_comp_antipodeAlgHom) x) r hr

end QuadraticTwist
