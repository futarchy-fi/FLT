/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureHopfOperations

/-!
# The Hopf counit and inverse retain the original subgroup evaluations

The affine evaluation map is the actual integral section. Consequently the
recovered counit evaluates at zero, and the antipode evaluates at the original
negative subgroup point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- Taking spectrum of the original evaluation recovers its actual integral section. -/
theorem globalClosureEvaluation_spec (P : H) :
    Spec.map (CommRingCat.ofHom (globalClosureEvaluation A W H P).toRingHom) =
      integralSection A W H P ≫ (gluedClosure A W H 1 2).isoSpec.hom := by
  change Spec.map ((integralSection A W H P).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) =
    integralSection A W H P ≫ (gluedClosure A W H 1 2).toSpecΓ
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.toSpecΓ_naturality]

variable [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The actual Hopf counit is evaluation at the original subgroup zero. -/
theorem globalClosureHopf_counit_eq_evaluation :
    letI := globalClosureHopfAlgebra A W H hΔ
    Bialgebra.counitAlgHom A (GlobalClosure A W H) = globalClosureEvaluation A W H 0 := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  have he : Spec.map (CommRingCat.ofHom
      (Bialgebra.counitAlgHom A (GlobalClosure A W H)).toRingHom) =
      Spec.map (CommRingCat.ofHom (globalClosureEvaluation A W H 0).toRingHom) := by
    rw [globalClosureHopf_counit_spec, globalClosureEvaluation_spec]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective he))

/-- Evaluation after the recovered antipode is evaluation at the actual negative point. -/
theorem globalClosureHopf_antipode_evaluation (P : H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    (globalClosureEvaluation A W H P).comp
      (HopfAlgebra.antipodeAlgHom A (GlobalClosure A W H)) =
        globalClosureEvaluation A W H (-P) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  have he : Spec.map (CommRingCat.ofHom
      (((globalClosureEvaluation A W H P).comp
        (HopfAlgebra.antipodeAlgHom A (GlobalClosure A W H))).toRingHom)) =
      Spec.map (CommRingCat.ofHom (globalClosureEvaluation A W H (-P)).toRingHom) := by
    change Spec.map (CommRingCat.ofHom
      ((globalClosureEvaluation A W H P).toRingHom.comp
        (HopfAlgebra.antipodeAlgHom A (GlobalClosure A W H)).toRingHom)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, globalClosureEvaluation_spec,
      globalClosureHopf_antipode_spec, globalClosureEvaluation_spec, Category.assoc,
      Iso.hom_inv_id_assoc, ← Category.assoc, integralSection_negation]
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective he))

end FLT.Mazur.EllipticSubgroupChart
