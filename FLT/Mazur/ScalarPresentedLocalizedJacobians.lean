/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraGeneratorDifferentials
public import FLT.Mazur.ScalarSourceOpenLocalizedJacobians

/-!
# Localized coupled equations on algebra presentation coordinates

Algebra generation constructs both full-stalk differential spanning and
finite differentials. Thus a nonsingular coupled system on presentation
coordinates supplies an original-source neighborhood without any additional
finiteness, reducedness, or individual separability hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarPresentedLocalizedJacobians
open ScalarLocalizedSeparableEquations
variable {R T A B : Type} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R T] (M : Submonoid R) [IsLocalization M T]
  (σ : R →+* A) (φ : A →+* B) (Q : PrimeSpectrum B)
  (hM : ∀ m ∈ M, φ (σ m) ∉ Q.asIdeal)
  (n : ℕ) (z : Fin n → A) (F : Fin n → MvPolynomial (Fin n) T)
  (hz : let _ := σ.toAlgebra; Algebra.adjoin R (Set.range z) = ⊤)
  (hF : ∀ i, MvPolynomial.eval₂ (stalkMap M σ φ Q hM)
    (fun j ↦ algebraMap A (Localization.AtPrime (PrimeSpectrum.comap φ Q).asIdeal)
      (z j)) (F i) = 0)
  (hJ : Matrix.det (fun i j ↦ MvPolynomial.eval₂ (residueMap M σ φ Q hM)
    (fun k ↦ algebraMap B Q.asIdeal.ResidueField (φ (z k)))
    (MvPolynomial.pderiv j (F i))) ≠ 0)

include hz hF hJ in
/-- Presentation coordinates supply the missing full-stalk spanning condition automatically. -/
theorem condition : ScalarLocalizedJacobianTests.Condition (T := T) M σ φ Q := by
  let _ := σ.toAlgebra
  refine ⟨hM, n, z, F, ?_, hF, hJ⟩
  exact ScalarAlgebraGeneratorDifferentials.span_localization
    (PrimeSpectrum.comap φ Q).asIdeal.primeCompl z hz

include hz hF hJ in
/-- A presentation and coupled system construct an avoiding original differential annihilator. -/
theorem exists_annihilator :
    let _ := σ.toAlgebra
    ∃ a ∈ Module.annihilator A (KaehlerDifferential R A), φ a ∉ Q.asIdeal := by
  let _ := σ.toAlgebra
  exact ScalarLocalizedJacobianTests.exists_annihilator M σ φ Q
    (ScalarAlgebraGeneratorDifferentials.finite z hz)
    (condition M σ φ Q hM n z F hz hF hJ)

include hz hF hJ in
/-- Presentation equations yield an actual principal rigidity open in the unchanged source. -/
theorem exists_principal :
    let _ := σ.toAlgebra
    ∃ a : A, φ a ∉ Q.asIdeal ∧ Algebra.FormallyUnramified R (Localization.Away a) := by
  let _ := σ.toAlgebra
  exact ScalarLocalizedJacobianTests.exists_principal M σ φ Q
    (ScalarAlgebraGeneratorDifferentials.finite z hz)
    (condition M σ φ Q hM n z F hz hF hJ)

end FLT.Mazur.ScalarPresentedLocalizedJacobians
