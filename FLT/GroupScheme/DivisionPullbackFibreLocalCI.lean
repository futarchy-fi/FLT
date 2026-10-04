/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionResidueLocalCI
public import FLT.GroupScheme.NilpotentGeometricCharacteristic

/-! # Every fibre of the actual division pullback over a p-nilpotent test algebra -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K B k : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [Algebra R B]
  [Field k] [Algebra B k] [Algebra R k] [IsScalarTower R B k]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- In every field-valued fibre of the actual division pullback, every specified
polynomial presentation has a regular square localized kernel at every prime.
Nilpotence on the test algebra supplies the characteristic hypothesis. -/
theorem exists_division_pullback_fibre_regular_relations
    (hB : IsNilpotent (p : B)) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
    let A := k ⊗[B] (B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing)
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) k →ₐ[k] A), Function.Surjective f →
      ∀ (P : Ideal (MvPolynomial (Fin d) k)) [P.IsPrime], RingHom.ker f ≤ P →
      ∃ rs : List (Localization.AtPrime P), rs.length = d ∧
        Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (Localization.AtPrime P)) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
  dsimp only
  intro d f hf P _ hP
  have : CharP k p := (algebraMap B k).charP_of_nilpotent_natCast p Fact.out hB
  let xk := (IsScalarTower.toAlgHom R B k).comp x
  let : Algebra (X.level n).CoordinateRing k := xk.toRingHom.toAlgebra
  let : IsScalarTower (X.level n).CoordinateRing B k :=
    IsScalarTower.of_algebraMap_eq' rfl
  let e := Algebra.TensorProduct.cancelBaseChange (X.level n).CoordinateRing B k k
    (X.level (m + n)).CoordinateRing
  let g := e.toAlgHom.comp f
  have hg : Function.Surjective g := e.surjective.comp hf
  have hker : RingHom.ker g = RingHom.ker f := by
    ext q
    change e (f q) = 0 ↔ f q = 0
    exact map_eq_zero_iff e e.injective
  obtain ⟨rs, hlen, hgen, hreg⟩ :=
    X.exists_residue_division_regular_relations_atPrime m n xk g hg P (hker ▸ hP)
  exact ⟨rs, hlen, hker ▸ hgen, hreg⟩

end ThreeAdicPlan.PDivisibleSystem
