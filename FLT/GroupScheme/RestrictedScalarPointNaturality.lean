/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatRestrictedScalarExtension
public import FLT.GroupScheme.GenericMorphismScalarExtension

/-!
# Naturality of the actual scalar-extension point comparison

Integral tensor maps induce exactly the restricted original Galois-module maps.
The comparison is proved on original coordinates through the chosen algebraic
closure embedding; it therefore applies to prescribed maps of an extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K]
    (S L : Type) [CommRing S] [Field L] [PerfectField L] [Algebra R S]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]

/-- On original coordinates, the restricted model evaluates by the chosen
embedding of algebraic closures. -/
theorem FF.inversePoints_restrictedScalarExtension_tmul
    (X : FF R K) (x : X.Points) (a : X.CoordinateRing) :
    ((X.restrictedScalarExtension S L).inversePoints x).toMul (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) =
      AlgebraicClosure.map (algebraMap K L) ((X.inversePoints x).toMul (1 ⊗ₜ[R] a)) := by
  let W := X.galoisModule.restrict (algebraMap K L)
  let H := S ⊗[R] X.CoordinateRing
  let e : L ⊗[S] H ≃ₐc[L] W.GenericCoordinateAlgebra :=
    (X.scalarExtensionGenericEquiv S L).trans
      ((bialgebraBaseChangeEquiv K L (K ⊗[R] X.CoordinateRing)
        X.galoisModule.GenericCoordinateAlgebra X.genericCoordinates.symm).trans
          X.galoisModule.genericFieldChangeBialgEquiv)
  let p : Additive (L ⊗[S] H →ₐ[L] AlgebraicClosure L) :=
    BialgHom.precompPoints e.toBialgHom
      (GaloisModule.GenericFiber.evalAddHom L (AlgebraicClosure L) W x)
  have hp : (X.restrictedScalarExtension S L).points p = x := by
    change W.genericPoints (Additive.ofMul
      ((((MulActionHom.evalAlgHom _ L W (AlgebraicClosure L) x).comp e.toAlgEquiv.toAlgHom).comp
        e.symm.toAlgEquiv.toAlgHom))) = x
    have he : ((MulActionHom.evalAlgHom _ L W (AlgebraicClosure L) x).comp
        e.toAlgEquiv.toAlgHom).comp e.symm.toAlgEquiv.toAlgHom =
        MulActionHom.evalAlgHom _ L W (AlgebraicClosure L) x := by
      ext z
      exact congrArg (fun t : W.GenericCoordinateAlgebra ↦ t x) (e.apply_symm_apply z)
    rw [he]
    exact (AddEquiv.ofBijective
      (GaloisModule.GenericFiber.evalAddHom L (AlgebraicClosure L) W).toAddMonoidHom
      (GaloisModule.GenericFiber.evalAddHom_bijective L (AlgebraicClosure L) W)).symm_apply_apply x
  have hp' : (X.restrictedScalarExtension S L).inversePoints x = p := by
    apply (X.restrictedScalarExtension S L).points_bijective.1
    exact ((X.restrictedScalarExtension S L).pointsEquiv.apply_symm_apply x).trans hp.symm
  rw [hp']
  change e (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)) x = _
  change X.galoisModule.genericFieldChangeBialgEquiv (L := L)
    ((bialgebraBaseChangeEquiv K L (K ⊗[R] X.CoordinateRing)
      X.galoisModule.GenericCoordinateAlgebra X.genericCoordinates.symm)
        (X.scalarExtensionGenericEquiv S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)))) x = _
  rw [FF.scalarExtensionGenericEquiv_tmul]
  change algebraMap L (AlgebraicClosure L) (1 * algebraMap S L 1) *
    AlgebraicClosure.map (algebraMap K L) (X.genericCoordinates.symm (1 ⊗ₜ[R] a) x) = _
  simp only [map_one, mul_one, one_mul]
  congr 1
  have h := X.eval_genericCoordinates (X.genericCoordinates.symm (1 ⊗ₜ[R] a))
    (X.inversePoints x).toMul
  rw [X.genericCoordinates.apply_symm_apply] at h
  change (X.inversePoints x).toMul (1 ⊗ₜ[R] a) =
    X.genericCoordinates.symm (1 ⊗ₜ[R] a) (X.pointsEquiv (X.pointsEquiv.symm x)) at h
  rw [X.pointsEquiv.apply_symm_apply] at h
  exact h.symm

/-- The point map of the actual tensor morphism is restriction of the
original Galois-equivariant point map. -/
theorem ModelHom.genericHom_restrictedScalarExtension {X Y : FF R K} (f : ModelHom X Y) :
    genericHom (X := X.restrictedScalarExtension S L) (Y := Y.restrictedScalarExtension S L)
      (Bialgebra.TensorProduct.map (BialgHom.id S S) f) =
        (genericHom f).restrictScalars S L := by
  ext x
  apply (Y.restrictedScalarExtension S L).pointsEquiv.symm.injective
  change (Y.restrictedScalarExtension S L).pointsEquiv.symm
      ((Y.restrictedScalarExtension S L).pointsEquiv
        (BialgHom.precompPoints _ ((X.restrictedScalarExtension S L).inversePoints x))) = _
  rw [AddEquiv.symm_apply_apply]
  apply Additive.toMul.injective
  apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
  apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
  apply AlgHom.ext
  intro a
  change ((X.restrictedScalarExtension S L).inversePoints x).toMul (1 ⊗ₜ[S] (1 ⊗ₜ[R] f a)) =
    ((Y.restrictedScalarExtension S L).inversePoints (genericHom f x)).toMul
      (1 ⊗ₜ[S] (1 ⊗ₜ[R] a))
  rw [FF.inversePoints_restrictedScalarExtension_tmul,
    FF.inversePoints_restrictedScalarExtension_tmul]
  congr 1
  change (X.inversePoints x).toMul (1 ⊗ₜ[R] f a) =
    (Y.pointsEquiv.symm
      (Y.pointsEquiv (BialgHom.precompPoints f.baseChange (X.inversePoints x)))).toMul
      (1 ⊗ₜ[R] a)
  rw [Y.pointsEquiv.symm_apply_apply]
  rfl
end ThreeAdicPlan
