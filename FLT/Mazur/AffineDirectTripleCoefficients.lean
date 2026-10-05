/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTriplePureTransport

/-!
# Last-pair transport on arbitrary coefficient tensors

Tensor induction extends the pure transport formula to every coefficient.
The intermediate lemma specializes the scalar ring before substituting the
actual pullback sheaves, keeping the two scalar actions aligned.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDirectTripleTransport
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback AffineTensorCocycle AffineDirectTripleAdditivity
open AffineIteratedPullbackSections AffineLiftedOverlapCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem unbundled_ext {A B N T U C : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N] [Semiring T] [CommRing U]
    {P Q : ModuleCat U} [Module T P] [AddCommGroup C]
    (F : P ⟶ Q) (G : C →+ P) (K : B ⊗[A] N ≃+ C)
    (D : B ⊗[A] (B ⊗[A] N) ≃+ Q) (E : N ⊗[A] B ≃ₗ[B] B ⊗[A] N)
    (c : T) (t : B)
    (h : ∀ a n, F (c • G (K (a ⊗ₜ[A] n))) = D (a ⊗ₜ[A] E (n ⊗ₜ[A] t)))
    (x : B ⊗[A] N) :
    F (c • G (K x)) = D ((E.toLinearMap.restrictScalars A).lTensor B
      ((TensorProduct.assoc A B N B) (x ⊗ₜ[A] t))) := by
  induction x using TensorProduct.inductionOn with
  | tmul a n => exact h a n
  | add x y hx hy => simp only [map_add, smul_add, add_tmul, hx, hy]

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
omit [M.IsQuasicoherent] in
private theorem unbundled_triple_ext
    {P Q : (Spec (.of (Triple R S))).Modules} {C : Type u} [AddCommGroup C]
    (F : P ⟶ Q) (G : C →+ moduleSpecΓFunctor.obj P)
    (K : S ⊗[R] coefficients S M ≃+ C)
    (D : S ⊗[R] (S ⊗[R] coefficients S M) ≃+ moduleSpecΓFunctor.obj Q)
    (E : coefficients S M ⊗[R] S ≃ₗ[S] S ⊗[R] coefficients S M)
    (t : S)
    (h : ∀ (a : S) (n : coefficients S M),
      let z : coefficients S M ⊗[R] S := n ⊗ₜ[R] t
      moduleSpecΓFunctor.map F (coord3 R S t • G (K (a ⊗ₜ[R] n))) =
      D (a ⊗ₜ[R] E z)) (x : S ⊗[R] coefficients S M) :
    moduleSpecΓFunctor.map F (coord3 R S t • G (K x)) =
      D ((E.toLinearMap.restrictScalars R).lTensor S
        ((TensorProduct.assoc R S (coefficients S M) S) (x ⊗ₜ[R] t))) :=
  unbundled_ext (T := Triple R S) (moduleSpecΓFunctor.map F) G K D E
    (coord3 R S t) t h x

variable (e : AffineGeometricOverlap.Overlap R S M)

-- The concrete pullback specialization needs a deeper elaboration stack.
set_option maxRecDepth 2048 in
/-- The last-pair transport acts on the last two coefficient tensor slots. -/
theorem transport23_coefficients (t : S) (x : S ⊗[R] coefficients S M) :
    moduleSpecΓFunctor.map (transport23 R S M e).hom
      (coord3 R S t • mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
        (comparison (right R S) (pair12 R S).toRingHom
          (coord2 R S) (pair12_right R S) M).hom (secondSections R S M x)) =
      sections R S M
        (((AffineGeometricOverlap.tensorEquiv R S M e).toLinearMap.restrictScalars R).lTensor S
          ((TensorProduct.assoc R S (coefficients S M) S) (x ⊗ₜ[R] t))) :=
  unbundled_triple_ext R S M
    (P := ((pullback (Spec.map (CommRingCat.ofHom (coord2 R S)))).obj M))
    (transport23 R S M e).hom
    (mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
      (comparison (right R S) (pair12 R S).toRingHom
        (coord2 R S) (pair12_right R S) M).hom)
    (secondSections R S M) (sections R S M)
    (AffineGeometricOverlap.tensorEquiv R S M e) t
    (fun a n ↦ transport23_tmul R S M e a t n) x

end FLT.Mazur.AffineDirectTripleTransport
