/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupTensorEvaluation

/-!
# Comultiplication retains the original subgroup addition

Tensor evaluation at two original integral points, after the constructed Hopf
comultiplication, is evaluation at their actual subgroup sum.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The original affine comparison carries actual closure addition to affine multiplication. -/
@[reassoc] theorem closureAffineOverIso_addition :
    ((closureAffineOverIso A W H).hom ⊗ₘ (closureAffineOverIso A W H).hom).left ≫
      (closureAffineGrpObj A W H hΔ).mul.left =
      closureAddition A W H hΔ ≫ (gluedClosure A W H 1 2).isoSpec.hom := by
  let _ := closureCommGrpObj A W H hΔ
  let _ := closureAffineGrpObj A W H hΔ
  exact (congrArg Over.Hom.left
    (IsMonHom.mul_hom (closureAffineGroupIso A W H hΔ).hom.hom.hom)).symm

/-- Evaluation after comultiplication is evaluation at the original sum. -/
theorem globalClosureHopf_comul_evaluation (P Q : H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    (globalClosureTensorEvaluation A W H P Q).comp
      (Bialgebra.comulAlgHom A (GlobalClosure A W H)) =
        globalClosureEvaluation A W H (P + Q) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  have he : Spec.map (CommRingCat.ofHom
      (((globalClosureTensorEvaluation A W H P Q).comp
        (Bialgebra.comulAlgHom A (GlobalClosure A W H))).toRingHom)) =
      Spec.map (CommRingCat.ofHom (globalClosureEvaluation A W H (P + Q)).toRingHom) := by
    change Spec.map (CommRingCat.ofHom
      ((globalClosureTensorEvaluation A W H P Q).toRingHom.comp
        (Bialgebra.comulAlgHom A (GlobalClosure A W H)).toRingHom)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, globalClosureHopf_comul_spec,
      ← Category.assoc, globalClosureTensorEvaluation_spec, Category.assoc,
      closureAffineOverIso_addition, closureSectionPair_addition_assoc,
      globalClosureEvaluation_spec]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective he))

end FLT.Mazur.EllipticSubgroupChart
