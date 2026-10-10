/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCoefficientBranches

/-!
# Cartesian coefficient squares for arithmetic nodes and edges

Both objects of the complete cyclic diagram are actual base changes over
arbitrary coefficient rings. The edge comparison retains both projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial TensorProduct

universe u

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The coefficient extension square for the actual arithmetic node is cartesian. -/
theorem chartCoefficient_isPullback (t : R) :
    IsPullback (chartCoefficient R S t) (chartStructure S (algebraMap R S t))
      (chartStructure R t) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply IsPullback.flip
  exact IsPullback.of_iso_pullback ⟨(chartCoefficient_base R S t).symm⟩
    (chartBaseChangeIso R S t).symm (chartBaseChangeIso_inv_fst R S t)
    (chartBaseChangeIso_inv_snd R S t)

/-- The full arithmetic edge after extension is the original edge pullback. -/
def edgeBaseChangeIso : branchTorus S ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))) :=
  Scheme.Spec.mapIso (LaurentTensor.equivalence R S).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R S R[T;T⁻¹]).symm

/-- The torus base-change comparison retains the coefficient-base projection. -/
@[reassoc] theorem edgeBaseChangeIso_fst :
    (edgeBaseChangeIso R S).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S S[T;T⁻¹])) := by
  simp only [edgeBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (LaurentTensor.equivalence R S).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] R[T;T⁻¹]).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentTensor.equivalence_left R S

/-- The torus base-change comparison retains the original Laurent projection. -/
@[reassoc] theorem edgeBaseChangeIso_snd :
    (edgeBaseChangeIso R S).hom ≫ pullback.snd _ _ = edgeCoefficient R S := by
  simp only [edgeBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (LaurentTensor.equivalence R S).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R[T;T⁻¹] →ₐ[R] S ⊗[R] R[T;T⁻¹]).toRingHom) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact LaurentTensor.equivalence_right R S

/-- The full Laurent edge coefficient square is cartesian. -/
theorem edgeCoefficient_isPullback :
    IsPullback (edgeCoefficient R S)
      (Spec.map (CommRingCat.ofHom (algebraMap S S[T;T⁻¹])))
      (Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply IsPullback.flip
  refine IsPullback.of_iso_pullback ⟨?_⟩ (edgeBaseChangeIso R S)
    (edgeBaseChangeIso_fst R S) (edgeBaseChangeIso_snd R S)
  rw [← edgeBaseChangeIso_fst R S, ← edgeBaseChangeIso_snd R S,
    Category.assoc, Category.assoc]
  rw [pullback.condition]

end FLT.Mazur.PolygonSmoothing
