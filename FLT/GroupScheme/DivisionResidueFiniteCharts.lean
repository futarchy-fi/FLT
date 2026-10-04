/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionResidueLocalCI
public import FLT.Mathlib.RingTheory.Regular.FinitePresentationCover

/-! # A finite regular chart cover of the actual residue division fibre -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K k : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field k] [Algebra R k]
  {p height : ℕ} [Fact p.Prime] [CharP k p]
  (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- The actual residue fibre has a finite principal unit-ideal cover by square regular
presentations, preserving the given coordinates. This cover is over the residue field. -/
theorem exists_residue_division_finite_regular_charts
    (x : (X.level n).CoordinateRing →ₐ[R] k) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
    let A := k ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) k →ₐ[k] A), Function.Surjective f →
      ∃ (t : Finset (MvPolynomial (Fin d) k ⧸ RingHom.ker f))
        (a : t → MvPolynomial (Fin d) k) (qs : t → List (MvPolynomial (Fin d) k)),
        Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ ∧
        ∀ i, (qs i).length = d ∧ (∀ q ∈ qs i, f q = 0) ∧
          RingTheory.Sequence.IsRegular (Localization.Away (a i))
            ((qs i).map (algebraMap _ (Localization.Away (a i)))) ∧
          ∃ e : (Localization.Away (a i) ⧸
              Ideal.ofList ((qs i).map (algebraMap _ (Localization.Away (a i))))) ≃ₐ[k]
              Localization.Away (f (a i)),
            ∀ q : MvPolynomial (Fin d) k,
              e (Ideal.Quotient.mk _ (algebraMap _ _ q)) = algebraMap A _ (f q) := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
  dsimp only
  intro d f hf
  exact f.exists_finite_regular_presentation_cover hf d
    (fun P _ hP ↦ X.exists_residue_division_regular_relations_atPrime m n x f hf P hP)

end ThreeAdicPlan.PDivisibleSystem
