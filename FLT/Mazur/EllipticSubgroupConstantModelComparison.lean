/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupIntegralConstantCoordinates
public import FLT.Mazur.EllipticSubgroupFiniteFlatPoints
public import FLT.GroupScheme.ConstantGroupPoints

/-!
# The actual constant-to-closure model morphism

The integral evaluation map gives a model morphism whose generic map identifies
exactly the original subgroup points. Over a perfect field it is generically
bijective; integral bijectivity still requires local rigidity hypotheses.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.EllipticSubgroupChart

open ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The constant model maps to the actual closure through the original integral sections. -/
def globalClosureConstantModelHom :
    ModelHom (constantGroupModel A K H) (globalClosureFiniteFlatModel A W H hΔ) :=
  globalClosureIntegralConstantHopfMap A W H hΔ

/-- The model morphism retains the original integral coordinate map. -/
theorem globalClosureConstantModelHom_toAlgHom :
    (globalClosureConstantModelHom A W H hΔ).toAlgHom =
      globalClosureIntegralConstantMap A W H := rfl

/-- Its generic point map is exactly the original subgroup inclusion. -/
theorem globalClosureConstantModelHom_point (P : H) :
    genericHom (globalClosureConstantModelHom A W H hΔ) (constantGroupPoint A K H P) =
      globalClosureFiniteFlatPoint A W H hΔ P := by
  apply (globalClosureFiniteFlatModel A W H hΔ).integralPoints.injective
  rw [integralPoints_genericHom, constantGroupPoint_integral,
    globalClosureFiniteFlatPoint_integral]
  apply AlgHom.ext
  intro a
  change algebraMap A (AlgebraicClosure K)
    (ConstantGroupTensorEvaluation.evaluation A (Multiplicative H) (Multiplicative.ofAdd P)
      (globalClosureIntegralConstantMap A W H a)) =
    algebraMap A (AlgebraicClosure K) (globalClosureEvaluation A W H P a)
  rw [globalClosureIntegralConstantMap_evaluation]

variable [PerfectField K]

/-- The actual generic map is the comparison of the two original point equivalences. -/
theorem globalClosureConstantModelHom_generic (x : (constantGroupModel A K H).Points) :
    genericHom (globalClosureConstantModelHom A W H hΔ) x =
      globalClosureFiniteFlatPointEquiv A W H hΔ ((constantGroupPointEquiv A K H).symm x) := by
  obtain ⟨P, rfl⟩ := (constantGroupPointEquiv A K H).surjective x
  rw [AddEquiv.symm_apply_apply]
  exact globalClosureConstantModelHom_point A W H hΔ P

/-- The constant-to-closure comparison is an isomorphism on the entire generic point group. -/
theorem globalClosureConstantModelHom_generic_bijective :
    Function.Bijective (genericHom (globalClosureConstantModelHom A W H hΔ)) := by
  have he : (fun x => genericHom (globalClosureConstantModelHom A W H hΔ) x) =
      (fun x => globalClosureFiniteFlatPointEquiv A W H hΔ
        ((constantGroupPointEquiv A K H).symm x)) := by
    funext x
    exact globalClosureConstantModelHom_generic A W H hΔ x
  change Function.Bijective (fun x =>
    genericHom (globalClosureConstantModelHom A W H hΔ) x)
  rw [he]
  exact (globalClosureFiniteFlatPointEquiv A W H hΔ).bijective.comp
    (constantGroupPointEquiv A K H).symm.bijective

/-- Every geometric point of the actual closure has trivial Galois action. -/
theorem globalClosureFiniteFlatModel_smul
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (globalClosureFiniteFlatModel A W H hΔ).Points) : g • x = x := by
  obtain ⟨P, rfl⟩ := (globalClosureFiniteFlatPointEquiv A W H hΔ).surjective x
  exact globalClosureFiniteFlatPoint_fixed A W H hΔ P g

end FLT.Mazur.EllipticSubgroupChart
