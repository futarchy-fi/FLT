/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCompletedPoints
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-! # The complete adic topology of the original completed point group -/

@[expose] public noncomputable section
open PadicHodgeTheory
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Residue point groups have the discrete uniformity at each positive precision. -/
instance rationalPlaceResiduePointUniformSpace (s : ℕ) :
    UniformSpace (X.PointColimit (ComplexIntegerModPow p (s + 1))) := ⊥

instance rationalPlaceResiduePointDiscreteUniformity (s : ℕ) :
    DiscreteUniformity (X.PointColimit (ComplexIntegerModPow p (s + 1))) := ⟨rfl⟩

/-- The completed group inherits the uniformity of the product of residue groups. -/
instance rationalPlaceCompletedPointUniformSpace : UniformSpace X.RationalPlaceCompletedPoints :=
  inferInstanceAs (UniformSpace X.rationalPlaceCompletedPointSubgroup)

/-- Compatibility is a closed condition in the product of the original discrete residue groups. -/
theorem rationalPlaceCompletedPointSubgroup_isClosed :
    IsClosed (X.rationalPlaceCompletedPointSubgroup :
      Set (∀ s : ℕ, X.PointColimit (ComplexIntegerModPow p (s + 1)))) := by
  change IsClosed {x : ∀ s : ℕ, X.PointColimit (ComplexIntegerModPow p (s + 1)) |
    ∀ s, X.pointColimitMap
    (rationalPlaceIntegerModPowReduce p (Nat.le_succ (s + 1))) (x (s + 1)) = x s}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro s
  exact isClosed_eq ((continuous_of_discreteTopology).comp (continuous_apply (s + 1)))
    (continuous_apply s)

/-- Completeness follows from the closed inverse-limit equations, not finite residue cardinality. -/
instance rationalPlaceCompletedPointCompleteSpace : CompleteSpace X.RationalPlaceCompletedPoints :=
  (X.rationalPlaceCompletedPointSubgroup_isClosed).isComplete.completeSpace_coe

instance rationalPlaceCompletedPointT2Space : T2Space X.RationalPlaceCompletedPoints :=
  inferInstanceAs (T2Space X.rationalPlaceCompletedPointSubgroup)

/-- The coordinatewise convolution group law is continuous for the adic topology. -/
instance rationalPlaceCompletedPointIsTopologicalGroup :
    IsTopologicalGroup X.RationalPlaceCompletedPoints :=
  inferInstanceAs (IsTopologicalGroup X.rationalPlaceCompletedPointSubgroup)

/-- The original residue projections are uniformly continuous. -/
theorem rationalPlaceCompletedPointEval_uniformContinuous (s : ℕ) :
    UniformContinuous (X.rationalPlaceCompletedPointEval s) :=
  (Pi.uniformContinuous_proj _ s).comp uniformContinuous_subtype_val

/-- Equality at a specified precision defines an open neighborhood condition. -/
theorem rationalPlaceCompletedPointEval_fiber_isOpen (s : ℕ)
    (a : X.PointColimit (ComplexIntegerModPow p (s + 1))) :
    IsOpen {x : X.RationalPlaceCompletedPoints | X.rationalPlaceCompletedPointEval s x = a} :=
  (isOpen_discrete {a}).preimage (X.rationalPlaceCompletedPointEval_uniformContinuous s).continuous

end ThreeAdicPlan.PDivisibleSystem
