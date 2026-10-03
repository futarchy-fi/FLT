/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.CharacterLines
public import FLT.GaloisRepresentation.Extensions.ContinuousClass

/-!
# Transport of extension classes under coefficient changes

Equivariant additive equivalences of discrete coefficient groups transport
continuous cocycles and their splitting relation in both directions.
Scalar changes of coordinates are a special case when the action is linear.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G M N : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N]
    [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M] [DiscreteTopology N]
    (e : M ≃+ N) (he : ∀ (g : G) (x : M), e (g • x) = g • e x)

/-- Transport a continuous cocycle along a discrete coefficient equivalence. -/
def mapCoefficientCocycle (c : ContinuousCocycle G M) : ContinuousCocycle G N :=
  ⟨⟨fun g ↦ e (c.1 g), (continuous_of_discreteTopology (f := e)).comp c.1.continuous⟩,
    fun g h ↦ by simp only [ContinuousMap.coe_mk, c.2 g h, map_add, he]⟩

include he in
omit [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [DiscreteTopology M] [DiscreteTopology N] in
/-- An equivariant change of coefficients preserves and reflects splitting changes. -/
theorem mapCoefficient_equivalent_iff (c d : G → M) :
    SplittingEquivalent (fun g ↦ e (c g)) (fun g ↦ e (d g)) ↔ SplittingEquivalent c d := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨e.symm a, funext fun g ↦ e.injective ?_⟩
    have h := congrFun ha g
    simpa only [changeSplitting, map_add, map_sub, he, e.apply_symm_apply] using h
  · rintro ⟨a, rfl⟩
    refine ⟨e a, funext fun g ↦ ?_⟩
    simp only [changeSplitting, map_add, map_sub, he]

/-- The map on explicit continuous extension classes. -/
def mapCoefficientClass : ContinuousClass G M → ContinuousClass G N :=
  Quotient.map (mapCoefficientCocycle e he)
    (fun _ _ h ↦ (mapCoefficient_equivalent_iff e he _ _).mpr h)

omit [DiscreteTopology N] in
/-- Coefficient equivalences induce injective maps of continuous classes. -/
theorem mapCoefficientClass_injective : Function.Injective (mapCoefficientClass e he) := by
  intro x y
  induction x using Quotient.inductionOn with | h c =>
    induction y using Quotient.inductionOn with | h d =>
      intro h
      exact Quotient.sound ((mapCoefficient_equivalent_iff e he _ _).mp (Quotient.exact h))

include he in
omit [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [DiscreteTopology M] [DiscreteTopology N] in
/-- The inverse coefficient equivalence is equivariant too. -/
theorem coefficient_symm_equivariant (g : G) (x : N) :
    e.symm (g • x) = g • e.symm x := by
  apply e.injective
  simp only [e.apply_symm_apply, he]

/-- Every class is transported from the inverse coefficient group. -/
theorem mapCoefficientClass_surjective : Function.Surjective (mapCoefficientClass e he) := by
  intro z
  induction z using Quotient.inductionOn with | h c =>
    let d := mapCoefficientCocycle e.symm (coefficient_symm_equivariant e he) c
    refine ⟨continuousClassMk d, ?_⟩
    have hd : mapCoefficientCocycle e he d = c := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro g
      exact e.apply_symm_apply _
    exact congrArg continuousClassMk hd

/-- Discrete equivariant coefficient changes give equivalences on continuous classes. -/
noncomputable def coefficientClassEquiv : ContinuousClass G M ≃ ContinuousClass G N :=
  Equiv.ofBijective (mapCoefficientClass e he)
    ⟨mapCoefficientClass_injective e he, mapCoefficientClass_surjective e he⟩

section Scalar

variable {k : Type*} [Field k] [Module k M] [SMulCommClass G k M]

/-- A nonzero scalar change of coordinates is an additive equivalence. -/
def scalarCoefficientEquiv (a : kˣ) : M ≃+ M :=
  (LinearEquiv.smulOfUnit a : M ≃ₗ[k] M).toAddEquiv

omit [TopologicalSpace G] [TopologicalSpace M] [DiscreteTopology M] in
/-- Linear coefficient actions commute with rescaling, including the two-line basis factor. -/
theorem scalarCoefficientEquiv_equivariant (a : kˣ) (g : G) (x : M) :
    scalarCoefficientEquiv (M := M) a (g • x) = g • scalarCoefficientEquiv a x := by
  exact (smul_comm g (a : k) x).symm

end Scalar

end GaloisRepresentation.Extensions
