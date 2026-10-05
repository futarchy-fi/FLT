/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDirectTripleBalance
public import FLT.Mazur.AffineDirectTripleCoefficients

/-!
# The geometric cocycle in tensor coordinates

The direct third-coordinate chart detects the cocycle on all three tensor factors.
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

private theorem twice_tmul {R S N : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (E : N ⊗[R] S ≃ₗ[S] S ⊗[R] N) (n : N) (s t : S) :
    transportTwice E ((n ⊗ₜ[R] s) ⊗ₜ[R] t) =
      (E.toLinearMap.restrictScalars R).lTensor S
        ((TensorProduct.assoc R S N S) (E (n ⊗ₜ[R] s) ⊗ₜ[R] t)) := rfl

private theorem map_comp_eq {A : CommRingCat.{u}} {P Q W : (Spec A).Modules}
    (f : P ⟶ Q) (g : Q ⟶ W) (k : P ⟶ W) (h : f ≫ g = k)
    (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map g (moduleSpecΓFunctor.map f x) = moduleSpecΓFunctor.map k x := by
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, h]

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : AffineGeometricOverlap.Overlap R S M)

omit [M.IsQuasicoherent] in
/-- The geometric cocycle evaluated on a first-coordinate section. -/
theorem cocycle_section_apply (h : CocycleCompatible R S M e)
    (x : moduleSpecΓFunctor.obj (coordinate R S M (coord1 R S))) :
    moduleSpecΓFunctor.map (transport23 R S M e).hom
      (moduleSpecΓFunctor.map (transport R S M (pair12 R S) (coord1 R S) (coord2 R S)
        (pair12_left R S) (pair12_right R S) e).hom x) =
        moduleSpecΓFunctor.map (transport R S M (pair13 R S) (coord1 R S) (coord3 R S)
        (pair13_left R S) (pair13_right R S) e).hom x :=
  map_comp_eq (transport R S M (pair12 R S) (coord1 R S) (coord2 R S)
        (pair12_left R S) (pair12_right R S) e).hom (transport23 R S M e).hom
    (transport R S M (pair13 R S) (coord1 R S) (coord3 R S)
        (pair13_left R S) (pair13_right R S) e).hom h x

/-- The geometric cocycle identifies the scaled pair coefficient lifts. -/
theorem cocycle_scaled_sections (h : CocycleCompatible R S M e)
    (n : coefficients S M) (s t : S) :
    moduleSpecΓFunctor.map (transport23 R S M e).hom
      (coord3 R S t • mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
        (comparison (right R S) (pair12 R S).toRingHom
          (coord2 R S) (pair12_right R S) M).hom
          (secondSections R S M (AffineGeometricOverlap.tensorEquiv R S M e
            (n ⊗ₜ[R] s : coefficients S M ⊗[R] S)))) =
    coord2 R S s • mappedUnit (CommRingCat.ofHom (pair13 R S).toRingHom) _
      (comparison (right R S) (pair13 R S).toRingHom
        (coord3 R S) (pair13_right R S) M).hom
        (secondSections R S M (AffineGeometricOverlap.tensorEquiv R S M e
            (n ⊗ₜ[R] t : coefficients S M ⊗[R] S))) := by
  have h12 := AffineScaledTripleTransport.transport_smul_sections R S M e
    (pair12 R S) (coord1 R S) (coord2 R S) (pair12_left R S) (pair12_right R S)
    (coord3 R S t) (n ⊗ₜ[R] s : coefficients S M ⊗[R] S)
  have h13 := AffineScaledTripleTransport.transport_smul_sections R S M e
    (pair13 R S) (coord1 R S) (coord3 R S) (pair13_left R S) (pair13_right R S)
    (coord2 R S s) (n ⊗ₜ[R] t : coefficients S M ⊗[R] S)
  have hb := AffineDirectTripleBalance.firstLift_balance R S M n s t
  have hc := cocycle_section_apply R S M e h
    (@HSMul.hSMul (Triple R S) _
      (moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (coord1 R S)))).obj M))
      _ (coord3 R S t) (mappedUnit (CommRingCat.ofHom (pair12 R S).toRingHom) _
      (comparison (left R S) (pair12 R S).toRingHom
        (coord1 R S) (pair12_left R S) M).hom
        (firstSections R S M (n ⊗ₜ[R] s : coefficients S M ⊗[R] S))))
  have hA := congrArg (moduleSpecΓFunctor.map (transport23 R S M e).hom) h12.symm
  have hB := congrArg (moduleSpecΓFunctor.map
    (transport R S M (pair13 R S) (coord1 R S) (coord3 R S)
        (pair13_left R S) (pair13_right R S) e).hom) hb
  have hD := hB.trans h13
  have hE := hc.trans hD
  exact hA.trans hE

-- The concrete coefficient specialization needs a deeper elaboration stack.
set_option maxRecDepth 2048 in
/-- The geometric cocycle gives the full three-factor tensor cocycle. -/
theorem tensorEquiv_cocycle (h : CocycleCompatible R S M e)
    (n : coefficients S M) (s t : S) :
    transportTwice (R := R) (S := S) (N := coefficients S M)
      (AffineGeometricOverlap.tensorEquiv R S M e)
      ((n ⊗ₜ[R] s : coefficients S M ⊗[R] S) ⊗ₜ[R] t) =
        insertMiddle (R := R) (S := S) (N := coefficients S M) s
          (AffineGeometricOverlap.tensorEquiv R S M e (n ⊗ₜ[R] t : coefficients S M ⊗[R] S)) := by
  have h23 := transport23_coefficients R S M e t
    (AffineGeometricOverlap.tensorEquiv R S M e (n ⊗ₜ[R] s : coefficients S M ⊗[R] S))
  have hc := cocycle_scaled_sections R S M e h n s t
  have hd := directSections_insertMiddle R S M s
    (AffineGeometricOverlap.tensorEquiv R S M e (n ⊗ₜ[R] t : coefficients S M ⊗[R] S))
  have hT := congrArg (sections R S M)
    (twice_tmul (R := R) (S := S) (N := coefficients S M)
      (AffineGeometricOverlap.tensorEquiv R S M e) n s t)
  have hh := hT.trans (h23.symm.trans (hc.trans hd.symm))
  exact (sections R S M).injective hh

end FLT.Mazur.AffineDirectTripleTransport
