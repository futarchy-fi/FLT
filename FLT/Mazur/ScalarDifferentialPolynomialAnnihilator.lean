/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarDifferentialPrincipalRigidity

/-!
# Differential annihilators from equations of algebra generators

A common multiple of the evaluated derivatives annihilates every differential
when the corresponding roots generate the algebra. For finitely many generators,
the product is an explicit such multiple. Neither monic equations nor a
Noetherian scalar ring are required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarDifferentialPolynomialAnnihilator
open Polynomial
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/-- It suffices to annihilate the differentials of actual algebra generators. -/
theorem mem_annihilator_of_generators (s : Set A) (hs : Algebra.adjoin R s = ⊤)
    (a : A) (ha : ∀ x ∈ s, a • KaehlerDifferential.D R A x = 0) :
    a ∈ Module.annihilator A (KaehlerDifferential R A) := by
  have h : a • (LinearMap.id : KaehlerDifferential R A →ₗ[A]
      KaehlerDifferential R A) = 0 := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext_of_adjoin_eq_top s hs
    intro x hx
    exact ha x hx
  apply Module.mem_annihilator.mpr
  intro m
  exact LinearMap.congr_fun h m

/-- A polynomial relation gives its evaluated derivative as an annihilator of the root's d. -/
theorem derivative_smul_d_eq_zero (x : A) (P : R[X]) (hP : aeval x P = 0) :
    aeval x P.derivative • KaehlerDifferential.D R A x = 0 := by
  rw [← Derivation.map_aeval, hP, map_zero]

/-- Any common derivative multiple annihilates the whole relative differential module. -/
theorem common_multiple_mem_annihilator {ι : Type} (x : ι → A) (P : ι → R[X])
    (hx : Algebra.adjoin R (Set.range x) = ⊤) (hP : ∀ i, aeval (x i) (P i) = 0)
    (a : A) (ha : ∀ i, aeval (x i) (P i).derivative ∣ a) :
    a ∈ Module.annihilator A (KaehlerDifferential R A) := by
  apply mem_annihilator_of_generators (Set.range x) hx
  rintro _ ⟨i, rfl⟩
  obtain ⟨b, hb⟩ := ha i
  rw [hb, mul_comm, mul_smul, derivative_smul_d_eq_zero _ _ (hP i), smul_zero]

/-- The product of the generator derivatives is an actual source differential annihilator. -/
theorem product_mem_annihilator {ι : Type} [Fintype ι] (x : ι → A) (P : ι → R[X])
    (hx : Algebra.adjoin R (Set.range x) = ⊤) (hP : ∀ i, aeval (x i) (P i) = 0) :
    (∏ i, aeval (x i) (P i).derivative) ∈
      Module.annihilator A (KaehlerDifferential R A) := by
  apply common_multiple_mem_annihilator x P hx hP
  intro i
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- These equations construct a formally unramified principal localization. -/
theorem product_away_formallyUnramified {ι : Type} [Fintype ι]
    (x : ι → A) (P : ι → R[X])
    (hx : Algebra.adjoin R (Set.range x) = ⊤) (hP : ∀ i, aeval (x i) (P i) = 0) :
    Algebra.FormallyUnramified R (Localization.Away (∏ i, aeval (x i) (P i).derivative)) :=
  ScalarDifferentialPrincipalRigidity.away_formallyUnramified _
    (product_mem_annihilator x P hx hP)

end FLT.Mazur.ScalarDifferentialPolynomialAnnihilator
