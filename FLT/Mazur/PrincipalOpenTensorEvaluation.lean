/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorRestriction

/-!
# Evaluation on the original tensor principal open

The full coefficient evaluation of a localized section restricts to its
original unlocalized evaluation. The identity holds over any coefficient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] (x : A)
  (f : Localization.Away x →ₐ[R] S) (g : A →ₐ[R] S)
  (h : ∀ z, f (algebraMap A (Localization.Away x) z) = g z)

include h

/-- Localization evaluation and tensor restriction agree on all original functions. -/
theorem evaluation_restriction :
    (AlgHom.liftEquiv R S _ S f).comp (restriction (R := R) S x) =
      AlgHom.liftEquiv R S _ S g := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro z
  change AlgHom.liftEquiv R S _ S f (restriction (R := R) S x ((1 : S) ⊗ₜ[R] z)) = _
  simp only [restriction_tmul, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul]
  exact h z

/-- The complete localized spectrum evaluation includes as the original tensor evaluation. -/
@[reassoc] theorem evaluation_inclusion :
    Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv R S _ S f).toRingHom) ≫
      tensorInclusion (R := R) S x =
        Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv R S _ S g).toRingHom) := by
  rw [tensorInclusion, ← Spec.map_comp]
  exact congrArg (fun (e : S ⊗[R] A →ₐ[S] S) => Spec.map (CommRingCat.ofHom e.toRingHom))
    (evaluation_restriction x f g h)

end FLT.Mazur.PrincipalOpenTensor
