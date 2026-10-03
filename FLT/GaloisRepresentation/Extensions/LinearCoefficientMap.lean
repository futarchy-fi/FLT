/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.LinearContinuousClass

/-!
# Semilinear coefficient maps on continuous classes

Equivariance sends actual principal cocycles to principal cocycles. This
constructs scalar-extension maps without assuming exactness of cohomology.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {R S G M N : Type*} [Field R] [Field S] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
    [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
    [TopologicalSpace N] [DiscreteTopology N]
    {σ : R →+* S} (f : M →ₛₗ[σ] N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)

/-- An equivariant semilinear map induces a map on continuous cocycle submodules. -/
def linearCocycleMap : linearContinuousCocycles R G M →ₛₗ[σ]
    linearContinuousCocycles S G N where
  toFun c := ⟨⟨fun g ↦ f (c.1 g), (continuous_of_discreteTopology (f := f)).comp
    c.1.continuous⟩, fun g h ↦ by
      simp only [ContinuousMap.coe_mk, c.2 g h, map_add, hf]⟩
  map_add' c d := by apply Subtype.ext; apply ContinuousMap.ext; intro g; exact map_add f _ _
  map_smul' r c := by apply Subtype.ext; apply ContinuousMap.ext; intro g; exact f.map_smulₛₗ r _

/-- Principal cocycles map to principal cocycles via the same coefficient map. -/
theorem linearCocycleMap_principal : continuousPrincipals R G M ≤
    (continuousPrincipals S G N).comap (linearCocycleMap f hf) := by
  rintro c ⟨a, ha⟩
  refine ⟨f a, fun g ↦ ?_⟩
  change f (c.1 g) = _
  rw [ha, map_sub, hf]

/-- The induced semilinear map on linear continuous classes. -/
def linearCoefficientClass : LinearContinuousClass R G M →ₛₗ[σ]
    LinearContinuousClass S G N :=
  (continuousPrincipals R G M).mapQ (continuousPrincipals S G N)
    (linearCocycleMap f hf) (linearCocycleMap_principal f hf)

/-- On representatives the induced map is pointwise application of the coefficient map. -/
@[simp] theorem linearCoefficientClass_mk (c : linearContinuousCocycles R G M) :
    linearCoefficientClass f hf (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (linearCocycleMap f hf c) := rfl

end GaloisRepresentation.Extensions
