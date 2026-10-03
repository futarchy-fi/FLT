/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCochainComplex
public import FLT.LocalClassFieldTheory.InvariantStageTransition
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The filtered diagram of finite quotient complexes

Open normal subgroups are ordered by reverse inclusion. Intersection gives
a common refinement. Inflation defines a cocone in the continuous complex.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory Limits groupCohomology

variable (k G M : Type u) [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace G] [IsTopologicalGroup G]

local notation "ρ" => Representation.ofDistribMulAction k G M

/-- Finite quotient complexes, indexed by refinement of open normal subgroups. -/
def invariantStageDiagram :
    (OpenNormalSubgroup G)ᵒᵈ ⥤ CochainComplex (ModuleCat k) ℕ where
  obj N := inhomogeneousCochains (Rep.of ((ρ).quotientToInvariants (OrderDual.ofDual N).toSubgroup))
  map {N P} f := invariantStageTransition k G M
    (N := (OrderDual.ofDual N).toSubgroup) (P := (OrderDual.ofDual P).toSubgroup) (leOfHom f)
  map_id N := invariantStageTransition_refl k G M (OrderDual.ofDual N).toSubgroup
  map_comp {N P Q} f g := (invariantStageTransition_comp k G M
    (N := (OrderDual.ofDual N).toSubgroup) (P := (OrderDual.ofDual P).toSubgroup)
    (Q := (OrderDual.ofDual Q).toSubgroup) (leOfHom f) (leOfHom g)).symm

variable [TopologicalSpace M] [DiscreteTopology M]
  [CompactSpace G] [TotallyDisconnectedSpace G] [ContinuousSMul G M]

set_option backward.isDefEq.respectTransparency false in
/-- Inflation with codomain restricted to continuous cochains. -/
def continuousStageInflation (N : OpenNormalSubgroup G) :
    (invariantStageDiagram k G M).obj N ⟶ continuousCochains k G M :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    (((invariantCochainInflation k G M N.toSubgroup).f n).hom.codRestrict _
      (continuous_invariantCochainInflation k G M N n))) (fun n => by
        ext c : 2
        apply Subtype.ext
        simp only [continuousCochains, invariantStageDiagram, CochainComplex.of_d]
        change (inhomogeneousCochains.d (Rep.of ρ) n).hom
            (((invariantCochainInflation k G M N.toSubgroup).f n).hom c) =
          ((invariantCochainInflation k G M N.toSubgroup).f (n + 1)).hom
            ((inhomogeneousCochains.d (Rep.of ((ρ).quotientToInvariants N.toSubgroup)) n).hom c)
        exact (invariantCochainInflation_d k G M N.toSubgroup n c).symm)


/-- Continuous inflation is still injective. -/
theorem continuousStageInflation_injective (N : OpenNormalSubgroup G) (n : ℕ) :
    Function.Injective ((continuousStageInflation k G M N).f n).hom := by
  intro c d h
  exact invariantCochainInflation_injective k G M N.toSubgroup n (congrArg Subtype.val h)

/-- Refinement is compatible with continuous inflation. -/
theorem continuousStageInflation_naturality {N P : (OpenNormalSubgroup G)ᵒᵈ}
    (f : N ⟶ P) :
    (invariantStageDiagram k G M).map f ≫ continuousStageInflation k G M P =
      continuousStageInflation k G M N := by
  ext n c
  rfl

/-- The continuous complex is a cocone over the filtered stage diagram. -/
def continuousStageCocone : Cocone (invariantStageDiagram k G M) where
  pt := continuousCochains k G M
  ι := { app := continuousStageInflation k G M
         naturality := fun _ _ f => by
           simpa using continuousStageInflation_naturality k G M f }

/-- Every continuous cochain comes from a stage of the diagram. -/
theorem continuousStageInflation_jointly_surjective (n : ℕ)
    (c : (continuousCochains k G M).X n) :
    ∃ (N : (OpenNormalSubgroup G)ᵒᵈ) (d : ((invariantStageDiagram k G M).obj N).X n),
      ((continuousStageInflation k G M N).f n).hom d = c := by
  obtain ⟨N, _, d, hd⟩ := exists_descended_invariant_cochain k G M
    (⟨c.val, c.property⟩ : C(Fin n → G, M))
  exact ⟨N, ⇑d, Subtype.ext (funext hd)⟩

end LocalClassFieldTheory
