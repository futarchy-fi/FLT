/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarStalkJacobianTests

/-!
# Rigidity neighborhoods from finiteness on a source principal open

Only the differentials on the chosen source open need be finite. A stalk
rigidity witness there gives an annihilator in the localized ring. Its
numerator, multiplied by the original denominator, defines a formally
unramified principal neighborhood in the original source.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenRigidity
variable {R A S : Type} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra A S] [Algebra R S] [IsScalarTower R A S]

/-- A localized differential annihilator yields an explicit original-source rigidity open. -/
theorem numerator_formallyUnramified (s : A) [IsLocalization.Away s S]
    (b : S) (hb : b ∈ Module.annihilator S (KaehlerDifferential R S)) :
    Algebra.FormallyUnramified R
      (Localization.Away (s * (IsLocalization.Away.sec s b).1)) := by
  let T := Localization.Away b
  let _ : Algebra.FormallyUnramified R T :=
    ScalarDifferentialPrincipalRigidity.away_formallyUnramified b hb
  let _ : IsLocalization.Away (s * (IsLocalization.Away.sec s b).1) T :=
    IsLocalization.Away.mul_of_associated s _ b
      (IsLocalization.Away.associated_sec_fst s b)
  exact Algebra.FormallyUnramified.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (s * (IsLocalization.Away.sec s b).1))
      T (Localization.Away (s * (IsLocalization.Away.sec s b).1))).restrictScalars R)

/-- Clearing an avoiding localized element gives an avoiding original-source denominator. -/
theorem numerator_not_mem (s : A) [IsLocalization.Away s S]
    (P : PrimeSpectrum S) (b : S) (hb : b ∉ P.asIdeal) :
    algebraMap A S (s * (IsLocalization.Away.sec s b).1) ∉ P.asIdeal := by
  rw [map_mul]
  intro h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact P.isPrime.ne_top (P.asIdeal.eq_top_of_isUnit_mem h
      (IsLocalization.Away.algebraMap_isUnit s))
  · rw [← IsLocalization.Away.sec_spec] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hb h
    · exact P.isPrime.ne_top (P.asIdeal.eq_top_of_isUnit_mem h
        (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit s).pow _))

/-- Local finite differentials spread stalk rigidity inside the original source principal open. -/
theorem exists_principal_neighborhood (s : A) [IsLocalization.Away s S]
    [Module.Finite S (KaehlerDifferential R S)] (P : PrimeSpectrum S)
    (hP : P ∈ Algebra.unramifiedLocus R S) :
    ∃ a : A, algebraMap A S a ∉ P.asIdeal ∧
      PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen s ∧
      Algebra.FormallyUnramified R (Localization.Away a) := by
  rw [Algebra.unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus] at hP
  obtain ⟨b, hb, hbP⟩ := Set.not_subset.mp hP
  refine ⟨s * (IsLocalization.Away.sec s b).1,
    numerator_not_mem s P b hbP, ?_, numerator_formallyUnramified s b hb⟩
  intro Q hQ hs
  exact hQ (Q.asIdeal.mul_mem_right _ hs)

end FLT.Mazur.ScalarSourceOpenRigidity

namespace FLT.Mazur.ScalarDifferentialPrincipalRigidity
open CategoryTheory AlgebraicGeometry SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Ring rigidity on a localization gives scheme rigidity on the same full principal open. -/
theorem principal_formallyUnramified_of_away {R : Type} [CommRing R]
    {X : Scheme.{0}} [IsAffine X] (σ : R →+* Γ(X, ⊤)) (a : Γ(X, ⊤))
    (h : let _ := σ.toAlgebra
      Algebra.FormallyUnramified R (Localization.Away a)) :
    FormallyUnramified ((X.basicOpen a).ι ≫ scalarMorphism σ) := by
  let _ := σ.toAlgebra
  let U := X.basicOpen a
  let _ : Algebra R Γ(U, ⊤) := (U.ι.appTop.hom.comp σ).toAlgebra
  let _ : IsScalarTower R Γ(X, ⊤) Γ(U, ⊤) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let _ := h
  let e := (IsLocalization.algEquiv (Submonoid.powers a)
    (Localization.Away a) Γ(U, ⊤)).restrictScalars R
  have hf : Algebra.FormallyUnramified R Γ(U, ⊤) :=
    Algebra.FormallyUnramified.of_equiv e
  rw [← scalarMorphism_comp]
  exact scalar_formallyUnramified _ hf

end FLT.Mazur.ScalarDifferentialPrincipalRigidity
