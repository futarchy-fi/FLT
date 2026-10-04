/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinatePoints
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! # Complete level topology on the original representing algebra

Finite coordinate rings are discrete for this topology. This is the topology of the
original level ideals; identifying it with a parameter-adic topology is a further theorem.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- The discrete uniformity used only on the original finite coordinate algebras. -/
local instance coordinateLevelUniformSpace (n : ℕ) : UniformSpace (X.level n).CoordinateRing := ⊥
local instance coordinateLevelDiscreteUniformity (n : ℕ) : DiscreteUniformity (X.level n).CoordinateRing := ⟨rfl⟩

/-- The coordinate limit has the uniformity induced from its discrete finite levels. -/
instance coordinateLimitUniformSpace : UniformSpace X.coordinateLimit :=
  inferInstanceAs (UniformSpace X.coordinateLimit)

/-- The original compatibility equations define a closed subset of the product. -/
theorem coordinateLimit_isClosed :
    IsClosed (X.coordinateLimit : Set (∀ n, (X.level n).CoordinateRing)) := by
  change IsClosed {x : ∀ n, (X.level n).CoordinateRing |
    ∀ (m n : ℕ) (h : m ≤ n), X.inclusion h (x n) = x m}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)

/-- Completeness uses closedness, not finiteness of the underlying coefficient ring. -/
instance coordinateLimitCompleteSpace : CompleteSpace X.coordinateLimit :=
  X.coordinateLimit_isClosed.isComplete.completeSpace_coe

instance coordinateLimitT2Space : T2Space X.coordinateLimit :=
  inferInstanceAs (T2Space X.coordinateLimit)

/-- Addition and multiplication are continuous in the original level topology. -/
instance coordinateLimitIsTopologicalRing : IsTopologicalRing X.coordinateLimit :=
  inferInstanceAs (IsTopologicalRing X.coordinateLimit.toSubring)

/-- All original finite evaluations are uniformly continuous. -/
theorem coordinateEval_uniformContinuous (n : ℕ) : UniformContinuous (X.coordinateEval n) :=
  (Pi.uniformContinuous_proj _ n).comp uniformContinuous_subtype_val

/-- A fiber of any original evaluation is open. -/
theorem coordinateEval_fiber_isOpen (n : ℕ) (a : (X.level n).CoordinateRing) :
    IsOpen {x : X.coordinateLimit | X.coordinateEval n x = a} :=
  (isOpen_discrete {a}).preimage (X.coordinateEval_uniformContinuous n).continuous

/-- Every open neighborhood contains a fiber of one original finite evaluation. -/
theorem coordinateEval_fiber_basis {U : Set X.coordinateLimit} (hU : IsOpen U)
    (x : X.coordinateLimit) (hx : x ∈ U) :
    ∃ n, {y : X.coordinateLimit | X.coordinateEval n y = X.coordinateEval n x} ⊆ U := by
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨s, u, hu, hs⟩ := isOpen_pi_iff.mp hV x.val hx
  refine ⟨s.sup id, fun y hy ↦ hs ?_⟩
  intro i hi
  have hi' : i ≤ s.sup id := Finset.le_sup (f := id) hi
  have he : X.coordinateEval i y = X.coordinateEval i x := by
    rw [← X.coordinateEval_inclusion hi' y, ← X.coordinateEval_inclusion hi' x, hy]
  change y.val i ∈ u i
  change y.val i = x.val i at he
  rw [he]
  exact (hu i hi).2

end ThreeAdicPlan.PDivisibleSystem
