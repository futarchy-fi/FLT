/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSquareZeroFormalSmoothness
public import FLT.GroupScheme.PDivisiblePointEquiv
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Nilpotent formal smoothness of the original p-divisible point functor -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Iterate the proved square-zero lifts through an arbitrary nilpotent ideal. -/
theorem pointColimitMap_surjective_nilpotent_quotient
    {B : Type} [CommRing B] [Algebra R B] (I : Ideal B)
    (hI : IsNilpotent I) (hB : IsNilpotent (p : B)) :
    Function.Surjective (X.pointColimitMap (Ideal.Quotient.mkₐ R I)) := by
  revert hB
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on I hI
  · intro B _ I hI _ hB
    apply X.pointColimitMap_surjective_squareZero (Ideal.Quotient.mkₐ R I)
      Ideal.Quotient.mk_surjective _ hB
    change RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥
    simpa only [Ideal.mk_ker] using hI
  · intro B _ I J hIJ h₁ h₂ _ hB
    let e : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      { (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun _ ↦ rfl }
    have hBI : IsNilpotent (p : B ⧸ I) := by
      simpa only [map_natCast] using hB.map (Ideal.Quotient.mk I)
    have hcomp : e.toAlgHom.comp ((Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R I)) =
        Ideal.Quotient.mkₐ R J := by ext b; rfl
    have hs := X.pointColimitMap_surjective_comp _ e.toAlgHom
      (X.pointColimitMap_surjective_comp _ _ (h₁ hB) (h₂ hBI)) (X.pointColimitEquiv e).surjective
    rwa [hcomp] at hs

/-- Formal smoothness on p-nilpotent test algebras, expressed by the original point functor. -/
theorem pointColimitMap_surjective_nilpotent
    {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : IsNilpotent (RingHom.ker q)) (hB : IsNilpotent (p : B)) :
    Function.Surjective (X.pointColimitMap q) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  have he : e.toAlgHom.comp (Ideal.Quotient.mkₐ R (RingHom.ker q)) = q := by ext b; rfl
  have hs := X.pointColimitMap_surjective_comp _ e.toAlgHom
    (X.pointColimitMap_surjective_nilpotent_quotient _ hJ hB) (X.pointColimitEquiv e).surjective
  rwa [he] at hs

/-- Every finite-level point lifts at a higher original level across a nilpotent thickening. -/
theorem exists_nilpotent_inclusion_lift
    {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : IsNilpotent (RingHom.ker q)) (hB : IsNilpotent (p : B))
    (n : ℕ) (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ (m : ℕ) (h : n ≤ m) (y : (X.level m).CoordinateRing →ₐ[R] B),
      q.comp y = x.comp (X.inclusion h).toAlgHom :=
  (X.pointColimitMap_surjective_iff q).mp
    (X.pointColimitMap_surjective_nilpotent q hq hJ hB) n x

end ThreeAdicPlan.PDivisibleSystem
