/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductOverlap
public import FLT.Mazur.AffineTripleOverlapPullback
public import FLT.Mazur.SchemeOverlapTransportComposition

/-!
# Pair transport from affine triple overlaps

The three pair projections map the affine triple overlap to the categorical
double overlap. Their projection squares define normalized transport of an
actual overlap to its coordinate sheaves. The affine cocycle comparison is
a separate obligation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps
open AffineTripleOverlapPullback SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A pair projection from the affine triple overlap to the actual double fiber product. -/
def fiberProductPair (t : S ⊗[R] S →ₐ[R] Triple R S) :=
  Spec.map (CommRingCat.ofHom t.toRingHom) ≫ (pullbackSpecIso R S S).inv

/-- The categorical pair projection has the specified first coordinate. -/
theorem fiberProductPair_fst (t : S ⊗[R] S →ₐ[R] Triple R S)
    (i : S →+* Triple R S) (hi : t.toRingHom.comp (left R S) = i) :
    fiberProductPair R S t ≫
        Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) = Spec.map (CommRingCat.ofHom i) := by
  rw [fiberProductPair, Category.assoc, pullbackSpecIso_inv_fst]
  exact spec_comp (left R S) t.toRingHom i hi

/-- The categorical pair projection has the specified second coordinate. -/
theorem fiberProductPair_snd (t : S ⊗[R] S →ₐ[R] Triple R S)
    (j : S →+* Triple R S) (hj : t.toRingHom.comp (right R S) = j) :
    fiberProductPair R S t ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) = Spec.map (CommRingCat.ofHom j) := by
  rw [fiberProductPair, Category.assoc, pullbackSpecIso_inv_snd]
  exact spec_comp (right R S) t.toRingHom j hj

variable (M : (Spec (.of S)).Modules)

/-- Transport a categorical overlap to two coordinate sheaves on the affine triple overlap. -/
def fiberProductTransport (t : S ⊗[R] S →ₐ[R] Triple R S) (i j : S →+* Triple R S)
    (hi : t.toRingHom.comp (left R S) = i) (hj : t.toRingHom.comp (right R S) = j)
    (e : FiberProductOverlap R S M) : coordinate R S M i ≅ coordinate R S M j :=
  normalize _ _ (fiberProductPair R S t) (Spec.map (CommRingCat.ofHom i))
    (Spec.map (CommRingCat.ofHom j)) (fiberProductPair_fst R S t i hi)
    (fiberProductPair_snd R S t j hj) M e

/-- Express tensor-chart normalization using the general scheme comparison. -/
theorem fromFiberProduct_eq_normalize (e : FiberProductOverlap R S M) :
    fromFiberProduct R S M e = normalize
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (pullbackSpecIso R S S).inv (Spec.map (CommRingCat.ofHom (left R S)))
      (Spec.map (CommRingCat.ofHom (right R S)))
      (pullbackSpecIso_inv_fst R S S) (pullbackSpecIso_inv_snd R S S) M e := rfl

end FLT.Mazur.AffineGeometricOverlap
