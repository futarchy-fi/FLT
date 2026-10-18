/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicIteration
public import FLT.Mazur.PolygonArithmeticHigherNodeStability

/-!
# Stabilization of the complete cyclic correction

Later rounds preserve all earlier smoothings, edges and whole-node factors.
The finite iteration therefore permits a different correction count at each order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (q : ι → R[T;T⁻¹]) (S : State R π ι)
  (r m : ℕ) (hm : m ≤ r)

include hm

/-- Every earlier node retains its exact smoothing after a later cyclic correction. -/
theorem State.step_parameter_stable (i : ι) :
    (S.step σ q r).parameter m i = S.parameter m i :=
  twoBranchCorrectionSmoothing_higher_stable R π m r hm _ _

/-- Both full puncture factors are stationary at every earlier arithmetic layer. -/
theorem State.punctureFactor_stable (i : ι) (a : Bool) :
    S.punctureFactor σ q r m i a = AlgEquiv.refl :=
  twoBranchCorrectionPunctureFactor_higher_stable R π m r hm _ _ a

/-- Every full earlier edge, including the closing edge, remains unchanged. -/
theorem State.step_edge_stable (i : ι) : (S.step σ q r).edge m i = S.edge m i := by
  change ((S.punctureFactor σ q r m (σ i) false).trans _).trans _ = _
  rw [S.punctureFactor_stable σ q r m hm, S.punctureFactor_stable σ q r m hm]
  rfl

/-- The whole earlier node factor is the canonical identification of equal parameters. -/
theorem State.nodeFactor_stable (i : ι) :
    S.nodeFactor σ q r m i =
      nodeParameterEquiv _ _ (S.step_parameter_stable σ q r m hm i) :=
  twoBranchCorrectionNodeFactor_higher_stable R π m r hm _ _

omit hm
variable (hS : S.Compatible) (ha : S.Annihilated) (r₀ : ℕ) (hr₀ : S.Normalized r₀)
local notation "I" => S.iterate σ hS ha r₀ hr₀

/-- Every full smoothing stabilizes once the iteration has reached its arithmetic order. -/
theorem State.iterate_parameter_stable {k l m : ℕ}
    (hkl : k ≤ l) (hm : m ≤ r₀ + k) (i : ι) :
    (I l).parameter m i = (I k).parameter m i := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_parameter_stable _ _ _ _ m (by omega)]
    exact ih

/-- All full edge substitutions stabilize at the same correction count. -/
theorem State.iterate_edge_stable {k l m : ℕ}
    (hkl : k ≤ l) (hm : m ≤ r₀ + k) (i : ι) :
    (I l).edge m i = (I k).edge m i := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iterate_succ, State.step_edge_stable _ _ _ _ m (by omega)]
    exact ih

end FLT.Mazur.PolygonArithmeticCyclic
