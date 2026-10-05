/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductPairTransport
public import FLT.Mazur.SchemeOverlapConjugation

/-!
# Canonical reconstruction overlaps in affine fiber-product charts

The canonical tensor-spectrum chart preserves canonical reconstruction overlaps
in both directions. The common base path is chosen through the fiber product.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The common path from the categorical double overlap to the affine base. -/
def canonicalFiberBase :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶ Spec (.of R) :=
  Limits.pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The same common path expressed on the tensor-spectrum chart. -/
def canonicalTensorBase : Spec (.of (S ⊗[R] S)) ⟶ Spec (.of R) :=
  (pullbackSpecIso R S S).inv ≫ canonicalFiberBase R S

/-- The left tensor projection has the chosen common base path. -/
theorem canonicalTensorBase_left :
    Spec.map (CommRingCat.ofHom (left R S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) = canonicalTensorBase R S := by
  rw [canonicalTensorBase, canonicalFiberBase, ← Category.assoc, pullbackSpecIso_inv_fst]

/-- The right tensor projection has the same common base path. -/
theorem canonicalTensorBase_right :
    Spec.map (CommRingCat.ofHom (right R S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) = canonicalTensorBase R S := by
  rw [canonicalTensorBase, canonicalFiberBase, Limits.pullback.condition,
    ← Category.assoc, pullbackSpecIso_inv_snd]

variable (A : (Spec (.of R)).Modules) {M : (Spec (.of S)).Modules}
variable (e : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj A ≅ M)

/-- Passing from the fiber product to its tensor chart preserves the canonical overlap. -/
theorem fromFiberProduct_chartOverlap :
    fromFiberProduct R S M
        (chartOverlap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Limits.pullback.fst _ _) (Limits.pullback.snd _ _) (canonicalFiberBase R S)
          rfl (Limits.pullback.condition.symm) A e) =
      chartOverlap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (left R S)))
        (Spec.map (CommRingCat.ofHom (right R S))) (canonicalTensorBase R S)
        (canonicalTensorBase_left R S) (canonicalTensorBase_right R S) A e := by
  rw [fromFiberProduct_eq_normalize]
  exact normalize_chartOverlap _ _ _ _ rfl (Limits.pullback.condition.symm)
    _ _ _ (pullbackSpecIso_inv_fst R S S) (pullbackSpecIso_inv_snd R S S)
    (canonicalTensorBase_left R S) (canonicalTensorBase_right R S) A e

/-- Recovering the categorical overlap preserves the canonical reconstruction overlap. -/
theorem toFiberProduct_chartOverlap :
    toFiberProduct R S M
        (chartOverlap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (left R S)))
          (Spec.map (CommRingCat.ofHom (right R S))) (canonicalTensorBase R S)
          (canonicalTensorBase_left R S) (canonicalTensorBase_right R S) A e) =
      chartOverlap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Limits.pullback.fst _ _) (Limits.pullback.snd _ _) (canonicalFiberBase R S)
        rfl (Limits.pullback.condition.symm) A e := by
  apply fromFiberProduct_injective R S M
  rw [fromFiberProduct_toFiberProduct, fromFiberProduct_chartOverlap]

end FLT.Mazur.AffineGeometricOverlap
