/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCyclicPolynomialSpanning
public import FLT.GroupScheme.RaynaudSpanningPresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Cyclic polynomial quotients are presentations

The relation quotient is spanned by digit monomials. A generated free
algebra of the corresponding rank is therefore isomorphic to that quotient.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CyclicPresentation
open MvPolynomial

variable {R ι : Type*} [CommRing R] [Fintype ι]
  (p : ℕ) (next : ι → ι) (a : ι → R)

/-- The ideal of cyclic p-power relations. -/
def relations : Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (fun i ↦ X i ^ p - C (a i) * X (next i)))

/-- The images of the variables in the explicitly constructed relation quotient. -/
def coordinate (i : ι) : MvPolynomial ι R ⧸ relations p next a :=
  Ideal.Quotient.mkₐ R (relations p next a) (X i)

omit [Fintype ι] in
/-- The quotient coordinates satisfy the defining cyclic relations. -/
theorem coordinate_relation (i : ι) :
    coordinate p next a i ^ p = a i • coordinate p next a (next i) := by
  have h : X i ^ p - C (a i) * X (next i) ∈ relations p next a :=
    Ideal.subset_span ⟨i, rfl⟩
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr h
  change (Ideal.Quotient.mkₐ R (relations p next a))
    (X i ^ p - C (a i) * X (next i)) = 0 at hz
  rw [map_sub, map_pow, map_mul] at hz
  apply sub_eq_zero.mp
  simpa only [coordinate, Algebra.smul_def, ← algebraMap_eq, AlgHom.commutes] using hz

omit [Fintype ι] in
/-- Evaluation in the quotient is the canonical quotient map. -/
theorem aeval_coordinate :
    aeval (coordinate p next a) = Ideal.Quotient.mkₐ R (relations p next a) := by
  ext i
  simp [coordinate]

/-- The relation quotient is spanned by its p^r digit monomials. -/
theorem quotient_digitSpan_eq_top (hp : 1 < p) :
    digitSpan (R := R) (coordinate p next a) p = ⊤ := by
  apply digitSpan_eq_top _ p hp next a (coordinate_relation p next a)
  rw [aeval_coordinate]
  exact Ideal.Quotient.mkₐ_surjective R _

variable {A : Type*} [CommRing A] [Algebra R A] (x : ι → A)
  (hrel : ∀ i, x i ^ p = a i • x (next i))

include hrel in
omit [Fintype ι] in
/-- Evaluation kills the relation ideal, derived from the actual coordinate equations. -/
theorem relations_le_ker : relations p next a ≤ RingHom.ker (aeval (R := R) x) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change aeval x (X i ^ p - C (a i) * X (next i)) = 0
  simp [hrel, Algebra.smul_def]

/-- The algebra map from the relation quotient to the actual coordinates. -/
def toCoordinates : (MvPolynomial ι R ⧸ relations p next a) →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (aeval x) (fun _ hf ↦ relations_le_ker p next a x hrel hf)

omit [Fintype ι] in
/-- The quotient map followed by coordinate evaluation is polynomial evaluation. -/
theorem toCoordinates_mk (f : MvPolynomial ι R) :
    toCoordinates p next a x hrel (Ideal.Quotient.mkₐ R (relations p next a) f) =
      aeval x f := rfl

variable [Nontrivial R] [IsNoetherianRing R] [Module.Free R A] [Module.Finite R A]

/-- Generation and the actual rank prove the polynomial quotient isomorphism. -/
def equiv (hp : 1 < p) (hsurj : Function.Surjective (aeval (R := R) x))
    (hrank : Module.finrank R A = p ^ Fintype.card ι) :
    (MvPolynomial ι R ⧸ relations p next a) ≃ₐ[R] A :=
  AlgEquiv.ofBijective (toCoordinates p next a x hrel) (by
    classical
    apply bijective_of_spanning_card
      (fun d : ι → Fin p ↦ CyclicPresentation.monomial (coordinate p next a) (fun i ↦ (d i).val))
      (quotient_digitSpan_eq_top p next a hp) (toCoordinates p next a x hrel).toLinearMap
    · intro y
      obtain ⟨f, rfl⟩ := hsurj y
      exact ⟨Ideal.Quotient.mkₐ R (relations p next a) f, rfl⟩
    · simpa only [Fintype.card_fun, Fintype.card_fin] using hrank.symm)

/-- The presentation isomorphism sends each polynomial variable to its actual coordinate. -/
theorem equiv_coordinate (hp : 1 < p) (hsurj : Function.Surjective (aeval (R := R) x))
    (hrank : Module.finrank R A = p ^ Fintype.card ι) (i : ι) :
    equiv p next a x hrel hp hsurj hrank (coordinate p next a i) = x i := by
  change aeval x (X i) = x i
  simp

end ThreeAdicPlan.CyclicPresentation
