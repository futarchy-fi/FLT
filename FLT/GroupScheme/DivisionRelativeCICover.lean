/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionRelativeFiniteCharts

/-! # Construct the complete relative division-chart presentation -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K B : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [Algebra R B]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- Construct the original polynomial presentation and its finite relative charts
internally. Every chart retains its coordinates and is regular on every field-valued
fibre; no presentation or regularity assumption is required from the caller. -/
theorem exists_division_relative_ci_cover
    (hB : IsNilpotent (p : B)) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
    let A := B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) B →ₐ[B] A), Function.Surjective f ∧
      ∃ (t : Finset (MvPolynomial (Fin d) B ⧸ RingHom.ker f))
        (a : t → MvPolynomial (Fin d) B) (rs : t → List (MvPolynomial (Fin d) B)),
        Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ ∧
        ∀ i, (rs i).length = d ∧ (∀ r ∈ rs i, f r = 0) ∧
          Ideal.ofList ((rs i).map (algebraMap _ (Localization.Away (a i)))) =
            (RingHom.ker f).map (algebraMap _ (Localization.Away (a i))) ∧
          (∀ (k : Type) [Field k] [Algebra B k],
            ∀ (P : Ideal (MvPolynomial (Fin d) k)) [P.IsPrime],
            RingHom.ker (baseChangePresentation k f) ≤ P →
            map (algebraMap B k) (a i) ∉ P →
            RingTheory.Sequence.IsRegular (Localization.AtPrime P)
              (((rs i).map (map (algebraMap B k))).map (algebraMap _ (Localization.AtPrime P)))) ∧
          ∃ e : (Localization.Away (a i) ⧸
              Ideal.ofList ((rs i).map (algebraMap _ (Localization.Away (a i))))) ≃ₐ[B]
              Localization.Away (f (a i)),
            ∀ s : MvPolynomial (Fin d) B,
              e (Ideal.Quotient.mk _ (algebraMap _ (Localization.Away (a i)) s)) =
                algebraMap A (Localization.Away (f (a i))) (f s) := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
  let : IsScalarTower R (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    IsScalarTower.of_algHom (X.reduction (Nat.le_add_left n m)).toAlgHom
  let : Module.Free R (X.level (m + n)).CoordinateRing := Module.free_of_flat_of_isLocalRing
  let : Module.FinitePresentation R (X.level (m + n)).CoordinateRing :=
    Module.finitePresentation_of_projective _ _
  let : Algebra.FinitePresentation (X.level n).CoordinateRing
      (X.level (m + n)).CoordinateRing :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  dsimp only
  let A := B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
  obtain ⟨d, f, hf, _⟩ := Algebra.FinitePresentation.out (R := B) (A := A)
  refine ⟨d, f, hf, ?_⟩
  exact X.exists_division_relative_finite_charts m n hB x f hf

end ThreeAdicPlan.PDivisibleSystem
