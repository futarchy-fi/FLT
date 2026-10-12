/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedEvaluationBaseChange
public import FLT.Mazur.SplitEvaluationBaseChange

/-!
# The actual bounded relations commute with arbitrary base change

For a finite flat finitely presented rank-d quotient, the constructed splitting
of degree-n evaluation identifies tensor extension of its relation module with
the actual degree-n relations over every coefficient algebra, whenever d ≤ n.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
universe u
variable (S T I : Type u) [CommRing S] [CommRing T] [Algebra S T]
  (J : Ideal (MvPolynomial I S)) (d n : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
  (hn : d ≤ n)

include hd hn in
/-- The scalar-extended relation submodule is the extended evaluation kernel. -/
theorem boundedRelationKernel_baseChange :
    (boundedRelationKernel S I J n).baseChange T =
      LinearMap.ker ((boundedQuotientEvaluation S I J n).baseChange T) := by
  obtain ⟨s, hs⟩ := boundedQuotientEvaluation_split S I J d n hd hn
  exact Approximation.splitEvaluation_baseChange_kernel _ s hs T

include hd hn in
/-- The ambient coefficient comparison takes all extended relations to the new relations. -/
theorem boundedRelationKernel_baseChange_map :
    ((boundedRelationKernel S I J n).baseChange T).map
        (boundedPolynomialBaseChangeEquiv S T I n).toLinearMap =
      boundedRelationKernel T I (J.map (MvPolynomial.map (algebraMap S T))) n := by
  rw [boundedRelationKernel_baseChange S T I J d n hd hn]
  exact boundedRelationKernel_map_baseChange S T I J n

/-- The tensor of the actual relation module is exactly the new bounded relation module. -/
def boundedRelationKernelBaseChangeEquiv :
    T ⊗[S] boundedRelationKernel S I J n ≃ₗ[T]
      boundedRelationKernel T I (J.map (MvPolynomial.map (algebraMap S T))) n := by
  let s := (boundedQuotientEvaluation_split S I J d n hd hn).choose
  have hs := (boundedQuotientEvaluation_split S I J d n hd hn).choose_spec
  exact (Approximation.splitEvaluationBaseChangeKernelEquiv _ s hs T).trans
    ((LinearEquiv.ofEq _ _ (boundedRelationKernel_comap_baseChange S T I J n).symm).trans
      ((boundedPolynomialBaseChangeEquiv S T I n).ofSubmodule' _))

include hd hn in
/-- No new tensor relations collapse under a possibly nonflat coefficient extension. -/
theorem boundedRelationKernel_baseChange_injective :
    Function.Injective ((boundedRelationKernel S I J n).subtype.baseChange T) := by
  obtain ⟨s, hs⟩ := boundedQuotientEvaluation_split S I J d n hd hn
  exact Approximation.splitEvaluation_baseChange_subtype_injective _ s hs T

end FLT.Mazur.HilbertChart
