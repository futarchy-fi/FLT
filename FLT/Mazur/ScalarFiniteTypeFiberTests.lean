/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarFiniteTypeJacobianEquations
public import FLT.Mazur.ScalarAlgebraGeneratorDifferentials
public import FLT.Mazur.ScalarStalkJacobianTests

/-!
# Full source stalk tests constructed from finite type and differential fibers

The polynomial coordinates and equations are constructed in the original
source. Only the differential fiber is tested in the target residue field.
Their exact equations and nonsingular Jacobian then kill the full stalk
differentials, including nilpotent directions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarFiniteTypeFiberTests
open MvPolynomial TensorProduct
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- The differential fiber uses the actual scalar action and the test prime's residue map. -/
def FiberVanishes (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  let _ := ((algebraMap B Q.asIdeal.ResidueField).comp φ).toAlgebra
  Subsingleton (Q.asIdeal.ResidueField ⊗[A] KaehlerDifferential R A)

/-- Finite type and a zero differential fiber construct exact full-stalk coupled equations. -/
theorem test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hft : let _ := σ.toAlgebra; Algebra.FiniteType R A)
    (h : FiberVanishes σ φ Q) : ScalarStalkJacobianTests.Test σ φ Q := by
  let _ := σ.toAlgebra
  let _ := ((algebraMap B Q.asIdeal.ResidueField).comp φ).toAlgebra
  let _ := hft
  let _ : Subsingleton (Q.asIdeal.ResidueField ⊗[A] KaehlerDifferential R A) := h
  obtain ⟨n, z, F, hz, hF, hJ⟩ :=
    ScalarFiniteTypeJacobianEquations.exists_equations (R := R) (A := A)
      (K := Q.asIdeal.ResidueField)
  refine ⟨n, z, F, ?_, ?_, hJ⟩
  · exact ScalarAlgebraGeneratorDifferentials.span_localization
      (PrimeSpectrum.comap φ Q).asIdeal.primeCompl z hz
  · intro i
    change algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (aeval z (F i)) = 0
    rw [hF, map_zero]

/-- The constructed system kills the full original-base stalk differentials. -/
theorem isUnramifiedAt (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hft : let _ := σ.toAlgebra; Algebra.FiniteType R A)
    (h : FiberVanishes σ φ Q) :
    let _ := σ.toAlgebra
    Algebra.IsUnramifiedAt R (PrimeSpectrum.comap φ Q).asIdeal :=
  ScalarStalkJacobianTests.isUnramifiedAt σ φ Q (test σ φ Q hft h)

/-- Finite type also supplies the differential finiteness needed for an original annihilator. -/
theorem exists_annihilator (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hft : let _ := σ.toAlgebra; Algebra.FiniteType R A)
    (h : FiberVanishes σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  let _ := hft
  exact ScalarStalkJacobianTests.exists_annihilator σ φ Q inferInstance (test σ φ Q hft h)

/-- The annihilator defines a principal rigidity neighborhood avoiding the test prime. -/
theorem exists_principal (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (hft : let _ := σ.toAlgebra; Algebra.FiniteType R A)
    (h : FiberVanishes σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨a, ha, hQa⟩ := exists_annihilator σ φ Q hft h
  exact ⟨a, hQa, ScalarDifferentialPrincipalRigidity.away_formallyUnramified a ha⟩

end FLT.Mazur.ScalarFiniteTypeFiberTests
