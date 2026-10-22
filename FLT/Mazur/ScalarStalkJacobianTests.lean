/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarStalkDifferentialJacobianRigidity

/-!
# Finite coupled tests in the source stalk

Tests retain the exact scalar map and the actual test prime. Their equations
and differential spanning are local; their residue Jacobian is nonsingular.
Finiteness is needed only when spreading the resulting stalk rigidity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarStalkJacobianTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Coupled equations and differential generators in the actual source stalk. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  let L := Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal
  ∃ (n : ℕ) (z : Fin n → A) (P : Fin n → MvPolynomial (Fin n) R),
    Submodule.span L (Set.range fun i ↦
      KaehlerDifferential.D R L (algebraMap A L (z i))) = ⊤ ∧
    (∀ i, algebraMap A L (MvPolynomial.eval₂ σ z (P i)) = 0) ∧
    Matrix.det (Matrix.map (fun i j ↦ MvPolynomial.eval₂ σ z (MvPolynomial.pderiv j (P i)))
      ((algebraMap B Q.asIdeal.ResidueField).comp φ)) ≠ 0

/-- The coupled test proves stalk rigidity without a finiteness assumption. -/
theorem isUnramifiedAt (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal := by
  let _ := σ.toAlgebra
  obtain ⟨n, z, P, hz, hP, hJ⟩ := h
  exact ScalarStalkDifferentialJacobianRigidity.isUnramifiedAt φ Q z P hz hP hJ

/-- Finite source differentials give an annihilator avoiding the tested prime. -/
theorem exists_annihilator (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hfg : let _ := σ.toAlgebra; Module.Finite A (KaehlerDifferential R A))
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  let _ := hfg
  obtain ⟨n, z, P, hz, hP, hJ⟩ := h
  exact ScalarStalkDifferentialJacobianRigidity.exists_annihilator φ Q z P hz hP hJ

end FLT.Mazur.ScalarStalkJacobianTests
