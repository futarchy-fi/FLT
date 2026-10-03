/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FixedCoefficientDifferential

/-!
# Refinement maps between invariant-coefficient complexes

For `P ≤ N`, pull back along `G/P → G/N` and include the `N`-invariants
in the `P`-invariants. These are actual cochain maps, compatible with inflation.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- Refinement includes the fixed coefficient modules. -/
def invariantStageInclusion {N P : Subgroup G} (h : P ≤ N) :
    Representation.invariants ((ρ).comp N.subtype) →ₗ[k]
      Representation.invariants ((ρ).comp P.subtype) :=
  Submodule.inclusion (fun _ hx g => hx ⟨g.val, h g.property⟩)

/-- The refinement map on the genuine quotient representation complexes. -/
def invariantStageTransition {N P : Subgroup G} [N.Normal] [P.Normal] (h : P ≤ N) :
    inhomogeneousCochains (Rep.of ((ρ).quotientToInvariants N)) ⟶
      inhomogeneousCochains (Rep.of ((ρ).quotientToInvariants P)) :=
  cochainsMap (QuotientGroup.map P N (MonoidHom.id G) h)
    (Rep.ofHom ⟨invariantStageInclusion k G M h, fun g => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective P g
      ext x
      rfl⟩)

/-- Refinement does not change the inflated cochain. -/
theorem invariantStageTransition_inflation {N P : Subgroup G} [N.Normal] [P.Normal]
    (h : P ≤ N) :
    invariantStageTransition k G M h ≫ invariantCochainInflation k G M P =
      invariantCochainInflation k G M N := by
  ext n c x
  rfl

/-- Refinement at an unchanged stage is the identity. -/
theorem invariantStageTransition_refl (N : Subgroup G) [N.Normal] :
    invariantStageTransition k G M (le_refl N) = 𝟙 _ := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply invariantCochainInflation_injective k G M N n
  exact congrArg (fun f => (f.f n).hom c)
    (invariantStageTransition_inflation k G M (le_refl N))

/-- Successive refinements compose. -/
theorem invariantStageTransition_comp {N P Q : Subgroup G}
    [N.Normal] [P.Normal] [Q.Normal] (h : P ≤ N) (h' : Q ≤ P) :
    invariantStageTransition k G M h ≫ invariantStageTransition k G M h' =
      invariantStageTransition k G M (h'.trans h) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply invariantCochainInflation_injective k G M Q n
  have he : (invariantStageTransition k G M h ≫ invariantStageTransition k G M h') ≫
      invariantCochainInflation k G M Q =
      invariantStageTransition k G M (h'.trans h) ≫ invariantCochainInflation k G M Q := by
    simp only [Category.assoc, invariantStageTransition_inflation]
  exact congrArg (fun f => (f.f n).hom c) he

end LocalClassFieldTheory
