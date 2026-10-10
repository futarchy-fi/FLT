/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupConstantModelComparison
public import FLT.GroupScheme.LocalModelIdentification

/-!
# Local rigidity of the original good-reduction subgroup closure

At a number-field completion in small ramification, a p-killed rational subgroup
has constant integral closure. The isomorphism is the previously constructed
section-evaluation morphism, rather than an unspecified generic identification.
-/

@[expose] public noncomputable section

open NumberField IsLocalRing ThreeAdicPlan

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (W : WeierstrassCurve (v.adicCompletionIntegers K))
  (H : AddSubgroup (W.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K))).toProjective.Point) [Finite H]
  (hΔ : IsUnit W.Δ) (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
  (hH : ∀ P : H, p • P = 0)

local notation "A" => v.adicCompletionIntegers K
local notation "L" => v.adicCompletion K

local instance : IsDedekindDomain A := IsPrincipalIdealRing.isDedekindDomain _

/-- Small ramification upgrades the actual integral evaluation morphism to an isomorphism. -/
def globalClosureLocalConstantIso :
    (constantGroupModel A L H).Iso (globalClosureFiniteFlatModel A W H hΔ) := by
  apply (existsUnique_iso_of_local_killed v p he ?_
    (genericHom (globalClosureConstantModelHom A W H hΔ))
    (globalClosureConstantModelHom_generic_bijective A W H hΔ)).choose
  intro x
  obtain ⟨P, rfl⟩ := (constantGroupPointEquiv A L H).surjective x
  rw [← map_nsmul, hH, map_zero]

/-- The isomorphism's pullback is exactly the original section-evaluation morphism. -/
theorem globalClosureLocalConstantIso_hom :
    (globalClosureLocalConstantIso v W H hΔ p he hH).toBialgHom =
      globalClosureConstantModelHom A W H hΔ := by
  apply genericHom_injective
  exact (existsUnique_iso_of_local_killed v p he
    (fun x => by
      obtain ⟨P, rfl⟩ := (constantGroupPointEquiv A L H).surjective x
      rw [← map_nsmul, hH, map_zero])
    (genericHom (globalClosureConstantModelHom A W H hΔ))
    (globalClosureConstantModelHom_generic_bijective A W H hΔ)).choose_spec.1

include hΔ he hH

/-- Every integral function on the finite subgroup lifts to its actual closure coordinates. -/
theorem globalClosureIntegralConstantMap_surjective_local :
    Function.Surjective (globalClosureIntegralConstantMap A W H) := by
  have h := (globalClosureLocalConstantIso v W H hΔ p he hH).surjective
  change Function.Surjective
    (globalClosureLocalConstantIso v W H hΔ p he hH).toBialgHom at h
  rw [globalClosureLocalConstantIso_hom] at h
  exact h

/-- The original integral closure is etale, derived from the local rigidity theorem. -/
theorem globalClosure_etale_local : Algebra.Etale A (GlobalClosure A W H) := by
  let : Algebra.Etale A (constantGroupModel A L H).CoordinateRing :=
    Algebra.Etale.of_equiv (constantGroupCoordinates A L H).symm
  exact Algebra.Etale.of_equiv
    (globalClosureLocalConstantIso v W H hΔ p he hH).symm.toAlgEquiv

end FLT.Mazur.EllipticSubgroupChart
