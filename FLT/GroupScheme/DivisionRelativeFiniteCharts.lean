/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionPrincipalRelations
public import FLT.Mathlib.RingTheory.Regular.FiniteRelativePresentationCover
public import FLT.Mathlib.RingTheory.MvPolynomial.PrincipalFibreRegularity

/-! # Finite relative fibre-regular charts of the actual division pullback -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K B : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [Algebra R B]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- The actual division pullback has finitely many square principal charts over
the original arbitrary test algebra. Their equations are regular at every point
of every field-valued fibre lying on the chart, and the denominators generate one. -/
theorem exists_division_relative_finite_charts
    (hB : IsNilpotent (p : B)) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
    let A := B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) B →ₐ[B] A), Function.Surjective f →
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
  let : Module.Finite (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    Module.Finite.of_restrictScalars_finite R _ _
  dsimp only
  intro d f hf
  have hp := X.exists_division_principal_relations m n hB x (d := d)
  dsimp only at hp
  obtain ⟨t, a, rs, hspan, hcharts⟩ := f.exists_finite_principal_presentation_cover hf d
    (fun Q _ ↦ by
      obtain ⟨a, rs, ha, hlen, hrs, hgen, _⟩ := hp f hf Q
      exact ⟨a, rs, ha, hlen, hrs, hgen⟩)
  refine ⟨t, a, rs, hspan, fun i ↦ ?_⟩
  obtain ⟨hlen, hrs, hgen, he⟩ := hcharts i
  refine ⟨hlen, hrs, hgen, ?_, he⟩
  intro k _ _ P _ hP ha
  exact isRegular_principal_presentation_fibre f hf (a i) (rs i) hlen hgen k P hP ha

end ThreeAdicPlan.PDivisibleSystem
