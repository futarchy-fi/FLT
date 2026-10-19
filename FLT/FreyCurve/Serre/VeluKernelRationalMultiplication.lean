/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalGroup

/-!
# Original geometric evaluations of the rational kernel multiplication

The rational Hopf multiplication on each original pair of labels is evaluation
at their sum. Both projections of the pair retain the original evaluations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped TensorProduct

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

attribute [local instance] primeKernelDescentHopfAlgebra

local notation "A" => PrimeKernelDescentAlgebra E p q hq hfixed

/-- Evaluation on an original pair of labels in the actual product algebra. -/
def primeKernelPairEvaluation (i j : ZMod p) : A ⊗[ℚ] A →ₐ[ℚ] AlgebraicClosure ℚ :=
  Algebra.TensorProduct.lift (primeKernelDescentEvaluation E p q hq hfixed i)
    (primeKernelDescentEvaluation E p q hq hfixed j) (fun _ _ ↦ Commute.all _ _)

/-- The actual descended comultiplication evaluates at the sum of the original labels. -/
theorem primeKernelPairEvaluation_comul (i j : ZMod p) :
    (primeKernelPairEvaluation E p q hq hfixed i j).comp (Bialgebra.comulAlgHom ℚ A) =
      primeKernelDescentEvaluation E p q hq hfixed (i + j) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  let _ := primeKernelLabelAction_continuous E p q hq hfixed
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.lift
    (MulActionHom.evalAlgHom (Field.absoluteGaloisGroup ℚ) ℚ (ZMod p) (AlgebraicClosure ℚ) i)
    (MulActionHom.evalAlgHom (Field.absoluteGaloisGroup ℚ) ℚ (ZMod p) (AlgebraicClosure ℚ) j)
    (fun _ _ ↦ Commute.all _ _)
    (GaloisModule.GenericFiber.comulAlgHom ℚ (AlgebraicClosure ℚ) (ZMod p) a) =
      primeKernelDescentEvaluation E p q hq hfixed (i + j) a
  rw [← GaloisModule.GenericFiber.tensorEquiv_eq_lift_eval,
    GaloisModule.GenericFiber.comulAlgHom_eval]
  rfl

/-- The original pair as a point of the categorical rational product. -/
def primeKernelPairSection (i j : ZMod p) : Spec (.of (AlgebraicClosure ℚ)) ⟶
    (primeKernelRationalScheme E p q hq hfixed ⊗
      primeKernelRationalScheme E p q hq hfixed).left :=
  Spec.map (CommRingCat.ofHom (primeKernelPairEvaluation E p q hq hfixed i j).toRingHom) ≫
    (pullbackSpecIso ℚ A A).inv

/-- The first projection retains the exact original first evaluation. -/
@[reassoc] theorem primeKernelPairSection_fst (i j : ZMod p) :
    primeKernelPairSection E p q hq hfixed i j ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (primeKernelDescentEvaluation E p q hq hfixed i).toRingHom) := by
  change primeKernelPairSection E p q hq hfixed i j ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap ℚ A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) = _
  rw [primeKernelPairSection, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change primeKernelPairEvaluation E p q hq hfixed i j (a ⊗ₜ[ℚ] 1) = _
  simp only [primeKernelPairEvaluation, Algebra.TensorProduct.lift_tmul, map_one]
  exact mul_one _

/-- The second projection retains the exact original second evaluation. -/
@[reassoc] theorem primeKernelPairSection_snd (i j : ZMod p) :
    primeKernelPairSection E p q hq hfixed i j ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (primeKernelDescentEvaluation E p q hq hfixed j).toRingHom) := by
  change primeKernelPairSection E p q hq hfixed i j ≫
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap ℚ A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) = _
  rw [primeKernelPairSection, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change primeKernelPairEvaluation E p q hq hfixed i j (1 ⊗ₜ[ℚ] a) = _
  simp only [primeKernelPairEvaluation, Algebra.TensorProduct.lift_tmul, map_one]
  exact one_mul _

/-- Rational scheme multiplication takes the original pair to its original sum label. -/
@[reassoc] theorem primeKernelPairSection_multiplication (i j : ZMod p) :
    primeKernelPairSection E p q hq hfixed i j ≫
      μ[primeKernelRationalScheme E p q hq hfixed].left =
        Spec.map (CommRingCat.ofHom
          (primeKernelDescentEvaluation E p q hq hfixed (i + j)).toRingHom) := by
  change (Spec.map _ ≫ (pullbackSpecIso ℚ A A).inv) ≫
    (pullbackSpecIso ℚ A A).hom ≫ Spec.map (CommRingCat.ofHom
      (Bialgebra.comulAlgHom ℚ A).toRingHom) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (primeKernelPairEvaluation_comul E p q hq hfixed i j)

end WeierstrassCurve.Velu
