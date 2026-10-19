/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelGeometricComparison

/-!
# The actual pullback of the rational source-kernel scheme

The geometric subgroup is the categorical base change of the rational spectrum.
The closed inclusion after scalar extension still has the original point sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The rational finite etale source-kernel scheme with its actual structure map. -/
def primeKernelRationalScheme : Over (Spec (.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap ℚ (PrimeKernelDescentAlgebra E p q hq hfixed))))

/-- The original geometric subgroup is the actual pullback of its rational spectrum. -/
def primeKernelPullbackIso : (primeKernelClosedSubgroup E p q hq).carrier.left ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
      (primeKernelRationalScheme E p q hq hfixed).hom :=
  primeKernelGeometricIso E p q hq hfixed ≪≫
    (pullbackSpecIso ℚ (AlgebraicClosure ℚ)
      (PrimeKernelDescentAlgebra E p q hq hfixed)).symm

/-- The comparison to the categorical pullback preserves the geometric base. -/
@[reassoc] theorem primeKernelPullbackIso_fst :
    (primeKernelPullbackIso E p q hq hfixed).hom ≫ pullback.fst _ _ =
      (primeKernelClosedSubgroup E p q hq).carrier.hom := by
  change _ ≫ pullback.fst _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ _))) = _
  simp only [primeKernelPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSpecIso_inv_fst']
  exact primeKernelGeometricIso_base E p q hq hfixed

/-- The projection of each geometric component is exactly its original rational evaluation. -/
@[reassoc] theorem primeKernelPullbackIso_component_snd (i : ZMod p) :
    (ConstantCyclicGroup.component (Spec (.of (AlgebraicClosure ℚ))) p i).left ≫
      (primeKernelPullbackIso E p q hq hfixed).hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom
          (primeKernelDescentEvaluation E p q hq hfixed i).toRingHom) := by
  change _ ≫ _ ≫ pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ _))) = _
  simp only [primeKernelPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSpecIso_inv_snd, primeKernelGeometricIso_component_assoc]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (Algebra.TensorProduct.liftEquivRight ℚ (AlgebraicClosure ℚ) _ _
    (primeKernelDescentEvaluation E p q hq hfixed i)) (1 ⊗ₜ[ℚ] a) = _
  exact one_mul _

/-- The scalar-extended evaluation still lands at precisely the original source point. -/
@[reassoc] theorem primeKernelScalarInclusion_evaluation (i : ZMod p) :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.liftEquivRight ℚ (AlgebraicClosure ℚ) _ _
        (primeKernelDescentEvaluation E p q hq hfixed i)).toRingHom) ≫
      primeKernelScalarInclusion E p q hq hfixed =
        ((affineRationalGroupSectionAddHom (E.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          (primeKernelParam E p q hq i)).toMul).left := by
  rw [← primeKernelGeometricIso_component, primeKernelScalarInclusion,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun f ↦ f.left) (primeKernelClosedSubgroup_component E p q hq i)

end WeierstrassCurve.Velu
