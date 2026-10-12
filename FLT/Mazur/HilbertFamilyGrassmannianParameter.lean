/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyFiniteQuotient
public import Mathlib.RingTheory.Grassmannian

/-!
# Grassmannian parameters of arbitrary finite flat Hilbert families

The bounded relation kernel defines an actual rank-d quotient Grassmannian point.
In degree d+1 this parameter determines the entire original ideal, over arbitrary
coefficient rings. This is a construction of Grassmannian-valued points; a scheme
representing this Grassmannian and the Hilbert immersion remain further work.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
universe u
variable (S I : Type u) [CommRing S] (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

include hd in
/-- The actual quotient has the required rank at every stalk of its coefficient base. -/
theorem finiteFlatQuotient_rankAtStalk (p : PrimeSpectrum S) :
    Module.rankAtStalk (R := S) (MvPolynomial I S ⧸ J) p = d := by
  let _ : Module.Projective S (MvPolynomial I S ⧸ J) :=
    Module.Flat.projective_of_finitePresentation
  rw [Module.rankAtStalk_eq]
  exact (polynomialQuotientBaseChangeEquiv I S p.asIdeal.ResidueField J).toLinearEquiv.finrank_eq
    |>.trans (hd p)

/-- The bounded relations define a genuine quotient Grassmannian parameter. -/
def finiteFlatGrassmannianParameter :
    Module.Grassmannian S (MvPolynomial.restrictTotalDegree I S (d + 1)) d := by
  let e := boundedRelationQuotientEquiv S I J d (d + 1) hd (Nat.le_succ d)
  let _ : Module.Projective S (MvPolynomial I S ⧸ J) :=
    Module.Flat.projective_of_finitePresentation
  refine { toSubmodule := boundedRelationKernel S I J (d + 1)
           finite_quotient := Module.Finite.equiv e.symm
           projective_quotient := Module.Projective.of_equiv e.symm
           rankAtStalk_eq := ?_ }
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans
    (finiteFlatQuotient_rankAtStalk S I J d hd p)

/-- The Grassmannian parameter retains exactly the actual truncated relation kernel. -/
theorem finiteFlatGrassmannianParameter_submodule :
    (finiteFlatGrassmannianParameter S I J d hd).toSubmodule =
      boundedRelationKernel S I J (d + 1) := rfl

variable (K : Ideal (MvPolynomial I S))
  [Module.FinitePresentation S (MvPolynomial I S ⧸ K)]
  [Module.Flat S (MvPolynomial I S ⧸ K)]
  (he : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      K.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

include hd he in
/-- Equality of constructed Grassmannian parameters forces equality of the full family ideals. -/
theorem finiteFlatGrassmannianParameter_injective
    (h : finiteFlatGrassmannianParameter S I J d hd =
      finiteFlatGrassmannianParameter S I K d he) : J = K := by
  have hk := congrArg Module.Grassmannian.toSubmodule h
  change boundedRelationKernel S I J (d + 1) = boundedRelationKernel S I K (d + 1) at hk
  calc
    J = Ideal.span ((fun p : MvPolynomial.restrictTotalDegree I S (d + 1) ↦ p.val) ''
        (boundedRelationKernel S I J (d + 1) : Set _)) :=
      (boundedRelationKernel_generates S I J d hd).symm
    _ = Ideal.span ((fun p : MvPolynomial.restrictTotalDegree I S (d + 1) ↦ p.val) ''
        (boundedRelationKernel S I K (d + 1) : Set _)) := by rw [hk]
    _ = K := boundedRelationKernel_generates S I K d he

end FLT.Mazur.HilbertChart
