/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousH1Comparison

/-!
# The explicit continuous splitting quotient is continuous H¹

The quotient comparison is induced by homogenization. Both injectivity and
surjectivity are proved on actual representatives.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

variable {k G M : Type u} [Field k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- Homogenization is linear on continuous cocycles. -/
def homogeneousOneCocycleLinear : linearContinuousCocycles k G M →ₗ[k]
    HomogeneousKernel (k := k) (G := G) (M := M) 1 where
  toFun c := homogeneousOneCocycle (linearCocycleForget c)
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    ext g h
    exact smul_add g (c.1 (g⁻¹ * h)) (d.1 (g⁻¹ * h))
  map_smul' a c := by
    apply Subtype.ext
    apply Subtype.ext
    ext g h
    exact smul_comm g a (c.1 (g⁻¹ * h))

/-- The linear comparison on cocycles. -/
noncomputable def continuousH1Linear : linearContinuousCocycles k G M →ₗ[k]
    continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M)) :=
  (homogeneousClass 1).comp homogeneousOneCocycleLinear

/-- The kernel of the comparison consists exactly of the continuous principals. -/
theorem continuousH1Linear_ker : LinearMap.ker (continuousH1Linear (k := k) (G := G) (M := M)) =
    continuousPrincipals k G M := by
  apply Submodule.ext
  intro c
  change continuousH1Class (k := k) (linearCocycleForget c) = 0 ↔ _
  exact continuousH1Class_eq_zero (linearCocycleForget c)

/-- Homogenization induces a linear map on the explicit continuous class quotient. -/
noncomputable def continuousH1Quotient : LinearContinuousClass k G M →ₗ[k]
    continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M)) :=
  (continuousPrincipals k G M).liftQ continuousH1Linear (by rw [continuousH1Linear_ker])

/-- The comparison on the quotient is injective. -/
theorem continuousH1Quotient_injective : Function.Injective
    (continuousH1Quotient (k := k) (G := G) (M := M)) := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  induction x using Quotient.inductionOn with | h c =>
    change continuousH1Class (linearCocycleForget c) = 0 ↔
      (Submodule.Quotient.mk c : LinearContinuousClass k G M) = 0
    rw [continuousH1Class_eq_zero, Submodule.Quotient.mk_eq_zero]
    rfl

/-- Every actual continuous H¹ class is represented by an explicit continuous cocycle. -/
theorem continuousH1Quotient_surjective : Function.Surjective
    (continuousH1Quotient (k := k) (G := G) (M := M)) := by
  intro x
  obtain ⟨z, rfl⟩ := homogeneousClass_surjective 1 x
  have hz : groupCohomology.IsCocycle₁ (inhomogeneousOne z.1) :=
    (homogeneousOne_cocycle_iff _).mp (by rw [homogeneousOne_inhomogeneousOne]; exact z.2)
  refine ⟨Submodule.Quotient.mk ⟨inhomogeneousOne z.1, hz⟩, ?_⟩
  change homogeneousClass 1 (homogeneousOneCocycle _) = homogeneousClass 1 z
  congr 1
  exact Subtype.ext (homogeneousOne_inhomogeneousOne z.1)

/-- The explicit linear quotient agrees with continuous cohomology in degree one. -/
noncomputable def continuousH1LinearEquiv : LinearContinuousClass k G M ≃ₗ[k]
    continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M)) :=
  LinearEquiv.ofBijective continuousH1Quotient
    ⟨continuousH1Quotient_injective, continuousH1Quotient_surjective⟩

/-- The original splitting quotient agrees with continuous cohomology in degree one. -/
noncomputable def continuousH1Equiv : ContinuousClass G M ≃
    continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M)) :=
  linearClassEquiv.symm.trans continuousH1LinearEquiv.toEquiv

/-- On representatives the comparison is the constructed homogeneous class. -/
theorem continuousH1Equiv_mk (c : ContinuousCocycle G M) :
    continuousH1Equiv (k := k) (continuousClassMk c) = continuousH1Class c := by
  have hc : continuousClassMk c = linearClassEquiv
      (Submodule.Quotient.mk (linearCocycleOf (k := k) c)) := rfl
  rw [hc]
  exact congrArg continuousH1LinearEquiv (linearClassEquiv.symm_apply_apply _)

end GaloisRepresentation.Extensions
