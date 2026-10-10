/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupHopfEvaluation

/-!
# Tensor evaluation is the actual integral section pair

The product of the two original algebra evaluations corresponds, under the
spectrum tensor comparison, to the pair of original integral sections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- Evaluation on the tensor product at the two original integral subgroup points. -/
def globalClosureTensorEvaluation (P Q : H) :
    GlobalClosure A W H ⊗[A] GlobalClosure A W H →ₐ[A] A :=
  Algebra.TensorProduct.productMap
    (globalClosureEvaluation A W H P) (globalClosureEvaluation A W H Q)

omit [Finite H] in
/-- Pure tensors evaluate as the product of the two original evaluations. -/
@[simp] theorem globalClosureTensorEvaluation_tmul (P Q : H) (a b : GlobalClosure A W H) :
    globalClosureTensorEvaluation A W H P Q (a ⊗ₜ[A] b) =
      globalClosureEvaluation A W H P a * globalClosureEvaluation A W H Q b := rfl

/-- Tensor evaluation followed by the first projection recovers the first section. -/
@[reassoc] theorem globalClosureTensorEvaluation_spec_fst (P Q : H) :
    Spec.map (CommRingCat.ofHom (globalClosureTensorEvaluation A W H P Q).toRingHom) ≫
      (pullbackSpecIso A (GlobalClosure A W H) (GlobalClosure A W H)).inv ≫
        pullback.fst _ _ =
      integralSection A W H P ≫ (gluedClosure A W H 1 2).isoSpec.hom := by
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((globalClosureTensorEvaluation A W H P Q).comp
      Algebra.TensorProduct.includeLeft).toRingHom)) = _
  rw [globalClosureTensorEvaluation, Algebra.TensorProduct.productMap_left]
  exact globalClosureEvaluation_spec A W H P

/-- Tensor evaluation followed by the second projection recovers the second section. -/
@[reassoc] theorem globalClosureTensorEvaluation_spec_snd (P Q : H) :
    Spec.map (CommRingCat.ofHom (globalClosureTensorEvaluation A W H P Q).toRingHom) ≫
      (pullbackSpecIso A (GlobalClosure A W H) (GlobalClosure A W H)).inv ≫
        pullback.snd _ _ =
      integralSection A W H Q ≫ (gluedClosure A W H 1 2).isoSpec.hom := by
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((globalClosureTensorEvaluation A W H P Q).comp
      Algebra.TensorProduct.includeRight).toRingHom)) = _
  rw [globalClosureTensorEvaluation, Algebra.TensorProduct.productMap_right]
  exact globalClosureEvaluation_spec A W H Q

/-- The tensor evaluation is the actual closure section pair in affine coordinates. -/
theorem globalClosureTensorEvaluation_spec (P Q : H) :
    Spec.map (CommRingCat.ofHom (globalClosureTensorEvaluation A W H P Q).toRingHom) ≫
      (pullbackSpecIso A (GlobalClosure A W H) (GlobalClosure A W H)).inv =
      closureSectionPair A W H P Q ≫
        ((closureAffineOverIso A W H).hom ⊗ₘ (closureAffineOverIso A W H).hom).left := by
  have hf : ((closureAffineOverIso A W H).hom ⊗ₘ
      (closureAffineOverIso A W H).hom).left ≫ pullback.fst _ _ =
      pullback.fst (closureToBase A W H 1 2) (closureToBase A W H 1 2) ≫
        (gluedClosure A W H 1 2).isoSpec.hom :=
    Over.tensorHom_left_fst _ _ _ _
  have hs : ((closureAffineOverIso A W H).hom ⊗ₘ
      (closureAffineOverIso A W H).hom).left ≫ pullback.snd _ _ =
      pullback.snd (closureToBase A W H 1 2) (closureToBase A W H 1 2) ≫
        (gluedClosure A W H 1 2).isoSpec.hom :=
    Over.tensorHom_left_snd _ _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, globalClosureTensorEvaluation_spec_fst, Category.assoc]
    exact ((congrArg (fun f => closureSectionPair A W H P Q ≫ f) hf).trans
      (closureSectionPair_fst_assoc A W H P Q _)).symm
  · rw [Category.assoc, globalClosureTensorEvaluation_spec_snd, Category.assoc]
    exact ((congrArg (fun f => closureSectionPair A W H P Q ≫ f) hs).trans
      (closureSectionPair_snd_assoc A W H P Q _)).symm

end FLT.Mazur.EllipticSubgroupChart
