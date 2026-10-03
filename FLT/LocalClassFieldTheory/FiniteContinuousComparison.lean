/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCohomologyColimit

/-!
# Continuous and ordinary cohomology of a finite discrete group

All cochains on finite powers of a discrete group are continuous. The
comparison is the identity on cochains and uses the actual differentials.
It works over any commutative ring, including the integers.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology HomologicalComplex

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G] [Finite G] [DiscreteTopology G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- On a discrete group, forgetting continuity is a linear equivalence in each degree. -/
def finiteContinuousCochainEquiv (n : ℕ) :
    continuousCochainModule k G M n ≃ₗ[k] ((Fin n → G) → M) where
  toFun := Subtype.val
  invFun f := ⟨f, continuous_of_discreteTopology⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite continuous complex is isomorphic to the ordinary inhomogeneous complex. -/
def finiteContinuousComplexIso :
    continuousCochains k G M ≅ inhomogeneousCochains (Rep.of ρ) :=
  Hom.isoOfComponents (fun n => (finiteContinuousCochainEquiv k G M n).toModuleIso)
    (fun i j _ => (continuousCochainsInclusion k G M).comm i j)

/-- The comparison does not change any cochain value. -/
theorem finiteContinuousComplexIso_apply (n : ℕ)
    (c : (continuousCochains k G M).X n) :
    (((finiteContinuousComplexIso k G M).hom).f n).hom c = c.val := rfl

/-- Continuous cohomology of a finite discrete group agrees with ordinary group cohomology. -/
def finiteContinuousCohomologyIso (n : ℕ) :
    continuousCohomology k G M n ≅ groupCohomology (Rep.of ρ) n :=
  (homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
    (finiteContinuousComplexIso k G M)

end LocalClassFieldTheory
