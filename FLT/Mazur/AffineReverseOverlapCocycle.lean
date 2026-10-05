/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePairUnitTransport
public import FLT.Mazur.AffineTripleUnitCoefficients

/-!
# Recovering the actual geometric cocycle from tensor transport

The tensor cocycle at the unit factors determines the actual sheaf cocycle:
all three maps are linear over the triple-overlap ring, and maps out of the
first coordinate pullback are determined on its unit sections.
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
private theorem twice_tmul_unit {R S N : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (E : N ⊗[R] S ≃ₗ[S] S ⊗[R] N) (n : N) :
    transportTwice E ((n ⊗ₜ[R] (1 : S)) ⊗ₜ[R] (1 : S)) =
      (E.toLinearMap.restrictScalars R).lTensor S
        ((TensorProduct.assoc R S N S) (E (n ⊗ₜ[R] (1 : S)) ⊗ₜ[R] (1 : S))) := rfl

private theorem comp_hom_ext {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : (Spec A).Modules) [M.IsQuasicoherent] {N P : (Spec B).Modules}
    (f : (pullback (Spec.map φ)).obj M ⟶ N) (g : N ⟶ P)
    (k : (pullback (Spec.map φ)).obj M ⟶ P)
    (h : ∀ n : moduleSpecΓFunctor.obj M,
      moduleSpecΓFunctor.map g (moduleSpecΓFunctor.map f (specUnit φ M n)) =
        moduleSpecΓFunctor.map k (specUnit φ M n)) : f ≫ g = k :=
  AffinePullbackHomExt.hom_ext φ M P (f ≫ g) k h

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
private theorem triple_comp_ext {P Q : (Spec (.of (Triple R S))).Modules}
    (f : coordinate R S M (coord1 R S) ⟶ P) (g : P ⟶ Q)
    (k : coordinate R S M (coord1 R S) ⟶ Q)
    (h : ∀ n : coefficients S M,
      moduleSpecΓFunctor.map g (moduleSpecΓFunctor.map f (unitSection R S M (coord1 R S) n)) =
        moduleSpecΓFunctor.map k (unitSection R S M (coord1 R S) n)) : f ≫ g = k :=
  comp_hom_ext (CommRingCat.ofHom (coord1 R S)) M f g k h

variable (e : AffineGeometricOverlap.Overlap R S M)

set_option maxRecDepth 2048 in
/-- The actual cocycle is detected on the first-coordinate unit sections. -/
theorem cocycleCompatible_of_unit
    (h : ∀ n : coefficients S M,
      moduleSpecΓFunctor.map (transport23 R S M e).hom
        (moduleSpecΓFunctor.map (transport R S M (pair12 R S) (coord1 R S) (coord2 R S)
          (pair12_left R S) (pair12_right R S) e).hom (unitSection R S M (coord1 R S) n)) =
      moduleSpecΓFunctor.map (transport R S M (pair13 R S) (coord1 R S) (coord3 R S)
        (pair13_left R S) (pair13_right R S) e).hom (unitSection R S M (coord1 R S) n)) :
    CocycleCompatible R S M e :=
  triple_comp_ext R S M
    (transport R S M (pair12 R S) (coord1 R S) (coord2 R S)
      (pair12_left R S) (pair12_right R S) e).hom (transport23 R S M e).hom
    (transport R S M (pair13 R S) (coord1 R S) (coord3 R S)
      (pair13_left R S) (pair13_right R S) e).hom h

-- Specializing the concrete chart maps requires a deeper elaboration stack.
set_option maxRecDepth 2048 in
/-- The tensor cocycle at unit factors implies the actual geometric cocycle. -/
theorem cocycleCompatible_of_tensor_unit
    (h : ∀ n : coefficients S M,
      transportTwice (R := R) (S := S) (N := coefficients S M)
        (AffineGeometricOverlap.tensorEquiv R S M e)
        ((n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S) ⊗ₜ[R] (1 : S)) =
      insertMiddle (R := R) (S := S) (N := coefficients S M) (1 : S)
        (AffineGeometricOverlap.tensorEquiv R S M e
          (n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S))) :
    CocycleCompatible R S M e := by
  apply cocycleCompatible_of_unit R S M e
  intro n
  have h12 := transport_unitSection R S M e (pair12 R S) (coord1 R S) (coord2 R S)
    (pair12_left R S) (pair12_right R S) n
  have h13 := transport_unitSection R S M e (pair13 R S) (coord1 R S) (coord3 R S)
    (pair13_left R S) (pair13_right R S) n
  have h23 := transport23_unit_coefficients R S M e
    (AffineGeometricOverlap.tensorEquiv R S M e
      (n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S))
  have hd := sections_insertMiddle_one R S M
    (AffineGeometricOverlap.tensorEquiv R S M e
      (n ⊗ₜ[R] (1 : S) : coefficients S M ⊗[R] S))
  have hT := congrArg (sections R S M)
    (twice_tmul_unit (R := R) (S := S) (N := coefficients S M)
      (AffineGeometricOverlap.tensorEquiv R S M e) n)
  have ht := congrArg (sections R S M) (h n)
  have hc := h23.trans (hT.symm.trans (ht.trans hd))
  have ha := congrArg (moduleSpecΓFunctor.map (transport23 R S M e).hom) h12
  exact ha.trans (hc.trans h13.symm)

/-- The full tensor cocycle and the actual geometric cocycle are equivalent. -/
theorem cocycleCompatible_iff_tensor : CocycleCompatible R S M e ↔
    ∀ (n : coefficients S M) (s t : S),
      transportTwice (R := R) (S := S) (N := coefficients S M)
        (AffineGeometricOverlap.tensorEquiv R S M e)
        ((n ⊗ₜ[R] s : coefficients S M ⊗[R] S) ⊗ₜ[R] t) =
      insertMiddle (R := R) (S := S) (N := coefficients S M) s
        (AffineGeometricOverlap.tensorEquiv R S M e (n ⊗ₜ[R] t : coefficients S M ⊗[R] S)) :=
  ⟨fun h ↦ tensorEquiv_cocycle R S M e h,
    fun h ↦ cocycleCompatible_of_tensor_unit R S M e (fun n ↦ h n 1 1)⟩

end FLT.Mazur.AffineDirectTripleTransport
