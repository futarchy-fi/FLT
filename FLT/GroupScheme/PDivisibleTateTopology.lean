/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateModule
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Instances.ZMod

/-! # The topology and continuous Galois action on Tate sequences

Finite point groups carry the discrete topology and the Tate module carries
the subspace topology in their product.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Geometric points of a finite level carry the discrete topology. -/
instance instTopologicalSpacePoints (n : ℕ) : TopologicalSpace (X.level n).Points := ⊥

/-- The declared finite-level topology is discrete. -/
instance instDiscreteTopologyPoints (n : ℕ) : DiscreteTopology (X.level n).Points := ⟨rfl⟩

/-- The inverse limit inherits the topology of the product of finite levels. -/
instance instTopologicalSpaceTate : TopologicalSpace X.tateSequences :=
  inferInstanceAs (TopologicalSpace {x : ∀ n, (X.level n).Points // x ∈ X.tateSequences})

/-- The resulting Tate topology is Hausdorff. -/
instance instT2SpaceTate : T2Space X.tateSequences :=
  inferInstanceAs (T2Space {x : ∀ n, (X.level n).Points // x ∈ X.tateSequences})

/-- Evaluation into every finite quotient is continuous. -/
theorem continuous_tateEval (n : ℕ) : Continuous (X.tateEval n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Continuity into the limit is equivalent to continuity of all evaluations. -/
theorem continuous_tate_iff {A : Type*} [TopologicalSpace A] (f : A → X.tateSequences) :
    Continuous f ↔ ∀ n, Continuous (fun a ↦ X.tateEval n (f a)) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- Addition is continuous for the inverse-limit topology. -/
instance instIsTopologicalAddGroupTate : IsTopologicalAddGroup X.tateSequences where
  continuous_add := (X.continuous_tate_iff _).mpr fun n ↦
    ((X.continuous_tateEval n).comp continuous_fst).add
      ((X.continuous_tateEval n).comp continuous_snd)
  continuous_neg := (X.continuous_tate_iff _).mpr fun n ↦
    (X.continuous_tateEval n).neg

/-- The actual coordinatewise Galois action is jointly continuous. -/
instance instContinuousSMulGaloisTate :
    ContinuousSMul (Field.absoluteGaloisGroup K) X.tateSequences where
  continuous_smul := (X.continuous_tate_iff _).mpr fun n ↦ by
    have : ContinuousSMul (Field.absoluteGaloisGroup K) (X.level n).Points :=
      (continuousSMulDiscrete_iff).mp inferInstance
    exact continuous_fst.smul ((X.continuous_tateEval n).comp continuous_snd)

end ThreeAdicPlan.PDivisibleSystem
