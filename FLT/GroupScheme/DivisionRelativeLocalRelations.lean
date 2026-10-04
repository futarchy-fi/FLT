/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionPullbackFibreLocalCI
public import FLT.GroupScheme.FinitePresentationPointCover
public import FLT.Mathlib.RingTheory.MvPolynomial.RelativeLocalRelations

/-! # Relative local equations for the actual division pullback -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K B : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [Algebra R B]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- At every point of the actual division pullback, an original polynomial
presentation has a square local kernel, regular modulo the contracted base prime.
The test algebra is arbitrary; no Noetherian assumption is imposed. -/
theorem exists_division_relative_local_relations
    (hB : IsNilpotent (p : B)) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
    let A := B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) B →ₐ[B] A), Function.Surjective f →
      ∀ (Q : Ideal A) [Q.IsPrime],
      let P := Q.comap (f : MvPolynomial (Fin d) B →+* A)
      let J := (Q.comap (algebraMap B A)).map (algebraMap B (Localization.AtPrime P))
      ∃ ws : List (Localization.AtPrime P), ws.length = d ∧
        Ideal.ofList ws = (RingHom.ker f).map (algebraMap _ _) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P ⧸ J)
          (ws.map (Ideal.Quotient.mk J)) := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
  let : IsScalarTower R (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    IsScalarTower.of_algHom (X.reduction (Nat.le_add_left n m)).toAlgHom
  let : Module.FaithfullyFlat (X.level n).CoordinateRing
      (X.level (m + n)).CoordinateRing := X.faithfullyFlat (Nat.le_add_left n m)
  let : Module.Free R (X.level (m + n)).CoordinateRing := Module.free_of_flat_of_isLocalRing
  let : Module.FinitePresentation R (X.level (m + n)).CoordinateRing :=
    Module.finitePresentation_of_projective _ _
  let : Algebra.FinitePresentation (X.level n).CoordinateRing
      (X.level (m + n)).CoordinateRing :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  dsimp only
  intro d f hf Q _
  apply exists_relative_local_regular_relations f hf Q
  let k := (Q.comap (algebraMap B _)).ResidueField
  intro P _ hP
  exact X.exists_division_pullback_fibre_regular_relations m n hB x
    (baseChangePresentation k f) (baseChangePresentation_surjective k f hf) P hP

end ThreeAdicPlan.PDivisibleSystem
