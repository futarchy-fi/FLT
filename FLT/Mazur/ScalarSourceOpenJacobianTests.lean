/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarSourceOpenEquationNeighborhoods

/-!
# Source-open equation tests without global differential finiteness

The equations are over the exact scalar ring on a chosen principal source
open. A prime on that open must lie over the actual inverse image of the
test prime. Finiteness is required only on this chosen open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarSourceOpenJacobianTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Finite local differentials and coupled equations, with the source prime identified exactly. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (s : A) (P : PrimeSpectrum (Localization.Away s)),
    PrimeSpectrum.comap (algebraMap A (Localization.Away s)) P = PrimeSpectrum.comap φ Q ∧
    Module.Finite (Localization.Away s) (KaehlerDifferential R (Localization.Away s)) ∧
    ScalarStalkJacobianTests.Test (algebraMap R (Localization.Away s))
      (RingHom.id (Localization.Away s)) P

/-- A source-open test constructs an avoiding rigidity neighborhood in the unchanged source. -/
theorem exists_principal (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨s, P, hP, hfg, hJ⟩ := h
  let _ := hfg
  obtain ⟨a, ha, _, hu⟩ := ScalarSourceOpenEquationNeighborhoods.of_jacobian
    (R := R) s (RingHom.id (Localization.Away s)) P hJ
  refine ⟨a, ?_, hu⟩
  change a ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact ha

end FLT.Mazur.ScalarSourceOpenJacobianTests

namespace FLT.Mazur.ScalarSourceOpenPolynomialTests
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]

/-- Separable scalar equations on a source open with finite local differentials. -/
def Test (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B) : Prop :=
  let _ := σ.toAlgebra
  ∃ (s : A) (P : PrimeSpectrum (Localization.Away s)),
    PrimeSpectrum.comap (algebraMap A (Localization.Away s)) P = PrimeSpectrum.comap φ Q ∧
    Module.Finite (Localization.Away s) (KaehlerDifferential R (Localization.Away s)) ∧
    ScalarStalkPolynomialTests.Test (algebraMap R (Localization.Away s))
      (RingHom.id (Localization.Away s)) P

/-- Local polynomial tests also yield original-source neighborhoods without global finiteness. -/
theorem exists_principal (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
    (h : Test σ φ Q) :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  obtain ⟨s, P, hP, hfg, hJ⟩ := h
  let _ := hfg
  obtain ⟨a, ha, _, hu⟩ := ScalarSourceOpenEquationNeighborhoods.of_polynomial
    (R := R) s (RingHom.id (Localization.Away s)) P hJ
  refine ⟨a, ?_, hu⟩
  change a ∉ (PrimeSpectrum.comap φ Q).asIdeal
  rw [← hP]
  exact ha

end FLT.Mazur.ScalarSourceOpenPolynomialTests
