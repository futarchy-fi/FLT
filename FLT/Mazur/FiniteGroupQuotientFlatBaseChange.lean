/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantFlatTensorComparison
public import FLT.Mazur.FiniteGroupAffineQuotient
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scheme-level flat base change of an affine finite-group quotient

The fixed-ring isomorphism induces an actual quotient-scheme isomorphism.
It identifies the quotient map with the tensor projection, and the original
quotient square is cartesian. The action on the tensor source is equivariant
for the projection to the original affine scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace FLT.Mazur.FiniteGroupQuotient

universe u
variable (G A : Type u) [Group G] [CommRing A] [MulSemiringAction G A]
variable (B : Type u) [CommRing B] [Algebra (invariantRing G A) B]

attribute [local instance] tensorAction

/-- The actual tensor source projects to the original affine scheme. -/
def tensorToOriginal : Spec (.of (B ⊗[invariantRing G A] A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- The map from the new affine base to the original invariant spectrum. -/
def tensorBaseMap : Spec (.of B) ⟶ affineQuotient G A :=
  Spec.map (CommRingCat.ofHom (algebraMap (invariantRing G A) B))

/-- The tensor-source projection intertwines the actual affine scheme actions. -/
@[reassoc]
lemma tensorToOriginal_equivariant (g : G) :
    actionMap G (B ⊗[invariantRing G A] A) g ≫ tensorToOriginal G A B =
      tensorToOriginal G A B ≫ actionMap G A g := by
  rw [actionMap, actionMap, tensorToOriginal, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  change tensorActionHom G A B g (1 ⊗ₜ[invariantRing G A] a) =
    1 ⊗ₜ[invariantRing G A] (g • a)
  exact tensorActionHom_tmul G A B g 1 a

/-- The tensor spectrum is the actual scheme pullback of the original quotient morphism. -/
theorem tensorSource_isPullback :
    IsPullback (tensorToOriginal G A B)
      (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[invariantRing G A] A))))
      (quotientMap G A) (tensorBaseMap G A B) := by
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (invariantRing G A) B A)).flip

variable [Finite G] [Module.Flat (invariantRing G A) B]

/-- The quotient of the actual base-changed affine source is the new base scheme. -/
def flatQuotientIso : affineQuotient G (B ⊗[invariantRing G A] A) ≅ Spec (.of B) :=
  Scheme.Spec.mapIso (tensorInvariantEquiv G A B).toCommRingCatIso.op

/-- The comparison identifies the actual quotient map with the tensor projection. -/
@[reassoc]
lemma quotientMap_flatQuotientIso_hom :
    quotientMap G (B ⊗[invariantRing G A] A) ≫ (flatQuotientIso G A B).hom =
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[invariantRing G A] A))) := by
  change Spec.map (CommRingCat.ofHom (inclusion G (B ⊗[invariantRing G A] A))) ≫
    Spec.map (CommRingCat.ofHom (tensorInvariantMap G A B)) = _
  rw [← Spec.map_comp]
  rfl

/-- The quotient comparison retains the actual cartesian base-change square. -/
theorem flatQuotient_isPullback :
    IsPullback (tensorToOriginal G A B)
      (quotientMap G (B ⊗[invariantRing G A] A) ≫ (flatQuotientIso G A B).hom)
      (quotientMap G A) (tensorBaseMap G A B) := by
  rw [quotientMap_flatQuotientIso_hom]
  exact tensorSource_isPullback G A B

end FLT.Mazur.FiniteGroupQuotient
