/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeCharpolyEquation
public import FLT.Mazur.SchemeRelationInvariantSpectrum
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# An original invariant polynomial from local bases of the whole relation

All coefficients descend to the unchanged full invariant ring. Reflexivity
makes the original source section a root. The polynomial is monic on each
free target chart; varying ranks do not imply that it is globally monic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.AffineLocallyFreeRelationCharpoly
open AffineCharpolyCoefficientGluing SchemeEffectiveEpiSections
universe u v
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The finite polynomial of multiplication along the entire original relation. -/
def relationPolynomial (s : Γ(A, ⊤)) : (Γ(A, ⊤))[X] :=
  polynomial p U hU hcover (q.appTop s)

/-- Its coefficients are the globally invariant coefficients constructed by rebasing. -/
theorem relationPolynomial_coeff (s : Γ(A, ⊤)) (n : ℕ) :
    (relationPolynomial p q U hU hcover s).coeff n =
      relationCoefficient p q U hU hcover s n := rfl

/-- On every free chart, including independently chosen ones, the polynomial is monic. -/
theorem relationPolynomial_locally_monic (V : A.affineOpens)
    (hV : AffineOpenNorm.HasBasis p V) (s : Γ(A, ⊤)) :
    ((relationPolynomial p q U hU hcover s).map V.1.ι.appTop.hom).Monic := by
  rw [relationPolynomial, polynomial_top p U hU hcover V hV]
  exact (AffineChosenBasisCharpoly.equation (p ∣_ V.1) hV _).1

variable (e : CategoryTheory.EquivalenceRelation p q)
include e

/-- Reflexivity descends the full-source Cayley-Hamilton equation to the source section. -/
theorem relationPolynomial_equation (s : Γ(A, ⊤)) :
    (relationPolynomial p q U hU hcover s).eval s = 0 := by
  have h := polynomial_equation p U hU hcover (q.appTop s)
  have hrp : e.r.appTop.hom.comp p.appTop.hom = RingHom.id _ := by
    ext t
    change (e.r ≫ p).appTop t = t
    rw [e.reflexivity₁]
    rfl
  have hrq : e.r.appTop (q.appTop s) = s := by
    change (e.r ≫ q).appTop s = s
    rw [e.reflexivity₂]
    rfl
  have hz := congrArg e.r.appTop.hom h
  change e.r.appTop.hom ((polynomial p U hU hcover (q.appTop s)).eval₂
    p.appTop.hom (q.appTop s)) = e.r.appTop.hom 0 at hz
  rw [hom_eval₂, hrp, hrq, map_zero] at hz
  exact hz

/-- The polynomial descends coefficient by coefficient to the full original invariant ring. -/
theorem exists_invariant_polynomial (s : Γ(A, ⊤)) :
    ∃ P : (compatibleFunctions p q)[X],
      P.map (compatibleFunctions p q).subtype = relationPolynomial p q U hU hcover s ∧
        P.eval₂ (compatibleFunctions p q).subtype s = 0 := by
  have hl : relationPolynomial p q U hU hcover s ∈
      Polynomial.lifts (compatibleFunctions p q).subtype := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, relationCoefficient_invariant p q U hU hcover e s n⟩, rfl⟩
  obtain ⟨P, hP⟩ := (mem_lifts _).mp hl
  refine ⟨P, hP, ?_⟩
  rw [← eval_map, hP]
  exact relationPolynomial_equation p q U hU hcover e s

end FLT.Mazur.AffineLocallyFreeRelationCharpoly
