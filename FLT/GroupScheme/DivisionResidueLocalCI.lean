/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionResidueRegularPresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.ResidueGeometricPoint

/-! # Regular presentations at every prime of the original division fibre -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K k : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field k] [Algebra R k]
  {p height : ℕ} [Fact p.Prime] [CharP k p]
  (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- Every prime of every specified polynomial presentation of the characteristic-p
residue division fibre has a regular square relation list over the original field. -/
theorem exists_residue_division_regular_relations_atPrime
    (x : (X.level n).CoordinateRing →ₐ[R] k) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) k →ₐ[k]
        k ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing),
      Function.Surjective f →
      ∀ (P : Ideal (MvPolynomial (Fin d) k)) [P.IsPrime], RingHom.ker f ≤ P →
      ∃ rs : List (Localization.AtPrime P), rs.length = d ∧
        Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (Localization.AtPrime P)) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
  dsimp only
  intro d f hf P _ hP
  let Ω := AlgebraicClosure P.ResidueField
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap k Ω).injective p
  obtain ⟨y, hy⟩ := exists_geometric_point_over_prime f hf P hP
  have h := X.exists_residue_division_regular_relations (Ω := Ω) m n x f hf y
  have key (Q : Ideal (MvPolynomial (Fin d) k)) [Q.IsPrime] (hQ : Q = P)
      (h : ∃ rs : List (Localization.AtPrime Q), rs.length = d ∧
        Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (Localization.AtPrime Q)) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime Q) rs) :
      ∃ rs : List (Localization.AtPrime P), rs.length = d ∧
        Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (Localization.AtPrime P)) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs := by
    subst Q
    exact h
  exact key _ hy h

end ThreeAdicPlan.PDivisibleSystem
