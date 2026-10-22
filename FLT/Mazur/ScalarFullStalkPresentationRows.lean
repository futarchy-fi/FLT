/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFullStalkPresentation
public import FLT.Mazur.ScalarJacobianRowSelection

/-!
# Coupled full-stalk systems from arbitrary relation families

Residue gradients spanning the coordinate space select a square nonsingular
subsystem. The selected equations remain in the actual presentation kernel,
so they hold in the full stalk, including its nilpotents. No bound on the
number of supplied relations or complete-intersection assumption is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFullStalkPresentationRows
open MvPolynomial ScalarLocalizedSeparableEquations ScalarFullStalkResidue
variable {R T A B κ : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)

/-- Spanning relation gradients construct the square coupled system at the full source stalk. -/
theorem condition (n : ℕ)
    (α : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      MvPolynomial (Fin n) T →ₐ[T]
        Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (hα : Function.Surjective α) (F : κ → MvPolynomial (Fin n) T)
    (hF : ∀ i, α (F i) = 0)
    (hspan : Submodule.span Q.asIdeal.ResidueField
      (Set.range fun i ↦ fun j ↦ toResidue φ Q (α (pderiv j (F i)))) = ⊤) :
    ScalarFullStalkJacobianTests.Condition (T := T) M σ φ Q := by
  obtain ⟨r, _, hr⟩ := ScalarJacobianRowSelection.exists_nonsingular n
    (fun i j ↦ toResidue φ Q (α (pderiv j (F i)))) hspan
  exact ScalarFullStalkPresentation.of_surjective M σ φ Q hM n α hα
    (fun i ↦ F (r i)) (fun i ↦ hF (r i)) hr

/-- The constructed subsystem proves original-base rigidity, retaining the complete stalk. -/
theorem isUnramifiedAt (n : ℕ)
    (α : let _ := (stalkMap (T := T) M σ φ Q hM).toAlgebra
      MvPolynomial (Fin n) T →ₐ[T]
        Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
    (hα : Function.Surjective α) (F : κ → MvPolynomial (Fin n) T)
    (hF : ∀ i, α (F i) = 0)
    (hspan : Submodule.span Q.asIdeal.ResidueField
      (Set.range fun i ↦ fun j ↦ toResidue φ Q (α (pderiv j (F i)))) = ⊤) :
    let _ := σ.toAlgebra
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal :=
  ScalarFullStalkJacobianTests.isUnramifiedAt M σ φ Q
    (condition M σ φ Q hM n α hα F hF hspan)

end FLT.Mazur.ScalarFullStalkPresentationRows
