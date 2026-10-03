/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousClassCoordinates
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Linear structure on continuous degree-one classes

Continuous cocycles form a submodule; the continuous principal cocycles
form a submodule of it. Its quotient is proved equivalent to the explicit
splitting quotient, without an assumption on the continuity of every orbit.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable (k G M : Type*) [Field k] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M]

instance : ContinuousConstSMul k M := ⟨fun _ ↦ continuous_of_discreteTopology⟩

/-- The submodule of continuous crossed homomorphisms. -/
def linearContinuousCocycles : Submodule k C(G, M) where
  carrier := {c | groupCohomology.IsCocycle₁ c}
  zero_mem' := by intro g h; simp
  add_mem' hc hd := by
    intro g h
    simp only [ContinuousMap.add_apply, hc g h, hd g h, smul_add]
    abel
  smul_mem' a c hc := by
    intro g h
    simp only [ContinuousMap.smul_apply, hc g h, smul_add, smul_comm g a]

/-- The principal continuous cocycles; discontinuous principal functions are not included. -/
def continuousPrincipals : Submodule k (linearContinuousCocycles k G M) where
  carrier := {c | ∃ a : M, ∀ g : G, c.1 g = g • a - a}
  zero_mem' := ⟨0, fun g ↦ by simp⟩
  add_mem' := by
    rintro c d ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun g ↦ ?_⟩
    change c.1 g + d.1 g = _
    rw [ha, hb, smul_add]
    abel
  smul_mem' := by
    rintro r c ⟨a, ha⟩
    refine ⟨r • a, fun g ↦ ?_⟩
    change r • c.1 g = _
    rw [ha, smul_sub, smul_comm g r]

/-- Continuous degree-one cohomology as a vector-space quotient. -/
abbrev LinearContinuousClass :=
  (linearContinuousCocycles k G M) ⧸ continuousPrincipals k G M

variable {k G M}

/-- The underlying continuous cocycle of a vector-space cocycle. -/
def linearCocycleForget (c : linearContinuousCocycles k G M) : ContinuousCocycle G M :=
  ⟨c.1, c.2⟩

/-- A continuous cocycle regarded as an element of the cocycle submodule. -/
def linearCocycleOf (c : ContinuousCocycle G M) : linearContinuousCocycles k G M :=
  ⟨c.1, c.2⟩

/-- Equality in the vector-space quotient is exactly change of splitting. -/
theorem linearClass_eq_iff (c d : linearContinuousCocycles k G M) :
    (Submodule.Quotient.mk c : LinearContinuousClass k G M) = Submodule.Quotient.mk d ↔
      SplittingEquivalent (fun g ↦ c.1 g) (fun g ↦ d.1 g) := by
  rw [Submodule.Quotient.eq]
  change (∃ a : M, ∀ g : G, c.1 g - d.1 g = g • a - a) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, funext fun g ↦ ?_⟩
    simp only [changeSplitting, smul_neg]
    calc
      d.1 g = c.1 g - (c.1 g - d.1 g) := by abel
      _ = c.1 g + (- (g • a) - -a) := by rw [ha]; abel
  · rintro ⟨a, ha⟩
    refine ⟨-a, fun g ↦ ?_⟩
    have h := congrFun ha g
    simp only [changeSplitting] at h
    simp only [h, smul_neg]
    abel

/-- Forget the linear presentation of a continuous cohomology class. -/
def linearClassForget : LinearContinuousClass k G M → ContinuousClass G M :=
  Quotient.lift (fun c ↦ continuousClassMk (linearCocycleForget c))
    (fun c d h ↦ (continuousClassMk_eq_iff _ _).mpr
      ((linearClass_eq_iff c d).mp (Quotient.sound h)))

/-- The two explicit quotients have the same equivalence relation. -/
theorem linearClassForget_injective : Function.Injective (linearClassForget (k := k)
    (G := G) (M := M)) := by
  intro x y
  induction x using Quotient.inductionOn with | h c =>
    induction y using Quotient.inductionOn with | h d =>
      intro h
      exact (linearClass_eq_iff c d).mpr (Quotient.exact h)

/-- Every explicit continuous class has a linear-quotient representative. -/
theorem linearClassForget_surjective : Function.Surjective (linearClassForget (k := k)
    (G := G) (M := M)) := by
  intro x
  induction x using Quotient.inductionOn with | h c =>
    exact ⟨Submodule.Quotient.mk (linearCocycleOf c), rfl⟩

/-- The linear quotient agrees with the previously defined splitting quotient. -/
noncomputable def linearClassEquiv : LinearContinuousClass k G M ≃ ContinuousClass G M :=
  Equiv.ofBijective linearClassForget
    ⟨linearClassForget_injective, linearClassForget_surjective⟩

/-- Scalar multiplication in the linear quotient is the actual coefficient change. -/
theorem linearClassEquiv_smul (a : kˣ) (x : LinearContinuousClass k G M) :
    linearClassEquiv ((a : k) • x) =
      mapCoefficientClass (scalarCoefficientEquiv (M := M) a)
        (scalarCoefficientEquiv_equivariant a) (linearClassEquiv x) := by
  induction x using Quotient.inductionOn with | h c =>
    rfl

end GaloisRepresentation.Extensions
