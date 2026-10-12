/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChart

/-!
# Reparametrize an entire tensor chart by an algebra equivalence

The actual spectrum isomorphism preserves both the new coefficient map
and every original chart function, including functions on exceptional fibers.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B] (e : S ⊗[R] A ≃ₐ[S] B)

/-- The entire reparametrized affine equation is the original tensor chart. -/
def algebraIso : Spec (.of B) ≅ Spec (.of (S ⊗[R] A)) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The comparison retains the actual extended coefficient structure. -/
@[reassoc] theorem algebraIso_structure :
    (algebraIso e).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact e.commutes

/-- The original projection evaluates every original function by the actual algebra equivalence. -/
@[reassoc] theorem algebraIso_projection :
    (algebraIso e).hom ≫ projection =
      Spec.map (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- A pure-tensor formula identifies the complete original coefficient projection. -/
theorem algebraIso_projection_of_tmul (p : A →+* B)
    (h : ∀ z : A, e ((1 : S) ⊗ₜ[R] z) = p z) :
    (algebraIso e).hom ≫ projection = Spec.map (CommRingCat.ofHom p) := by
  rw [algebraIso_projection]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact h

end FLT.Mazur.TensorOpenChart
