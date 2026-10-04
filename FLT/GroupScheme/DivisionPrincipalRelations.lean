/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionRelativeLocalRelations
public import FLT.Mathlib.RingTheory.Regular.RelativePrincipalRelations
public import FLT.Mathlib.RingTheory.Localization.PrincipalPresentationEquiv

/-! # Principal equations for the actual division pullback -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K B : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [Algebra R B]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

set_option maxHeartbeats 2000000 in
-- The spreading application compares the tensor, localized and quotient scalar structures.
set_option backward.isDefEq.respectTransparency false in
/-- Spread the original local equations to an actual principal chart. The full
kernel and number of equations are retained, and their reduction is regular at
the specified point. This does not yet assert regularity on every fibre of the chart. -/
theorem exists_division_principal_relations
    (hB : IsNilpotent (p : B)) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing B := x.toRingHom.toAlgebra
    let A := B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) B →ₐ[B] A), Function.Surjective f →
      ∀ (Q : Ideal A) [Q.IsPrime],
      let P := Q.comap (f : MvPolynomial (Fin d) B →+* A)
      let J := (Q.comap (algebraMap B A)).map (algebraMap B (Localization.AtPrime P))
      ∃ (a : MvPolynomial (Fin d) B) (rs : List (MvPolynomial (Fin d) B)),
        f a ∉ Q ∧ rs.length = d ∧ (∀ r ∈ rs, f r = 0) ∧
        Ideal.ofList (rs.map (algebraMap _ (Localization.Away a))) =
          (RingHom.ker f).map (algebraMap _ (Localization.Away a)) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P ⧸ J)
          ((rs.map (algebraMap _ (Localization.AtPrime P))).map (Ideal.Quotient.mk J)) ∧
        ∃ e : (Localization.Away a ⧸
            Ideal.ofList (rs.map (algebraMap _ (Localization.Away a)))) ≃ₐ[B]
            Localization.Away (f a),
          ∀ s : MvPolynomial (Fin d) B,
            e (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin d) B)
              (Localization.Away a) s)) = algebraMap A (Localization.Away (f a)) (f s) := by
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
  let A := B ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
  let P := Q.comap (f : MvPolynomial (Fin d) B →+* A)
  let J := (Q.comap (algebraMap B A)).map (algebraMap B (Localization.AtPrime P))
  have hlocal : ∃ ws : List (Localization.AtPrime P), ws.length = d ∧
      Ideal.ofList ws = (RingHom.ker f).map
        (algebraMap (MvPolynomial (Fin d) B) (Localization.AtPrime P)) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime P ⧸ J)
        (ws.map (Ideal.Quotient.mk J)) := by
    exact X.exists_division_relative_local_relations m n hB x f hf Q
  obtain ⟨ws, hlen, hgen, hreg⟩ := hlocal
  have hfg : (RingHom.ker f).FG := Algebra.FinitePresentation.ker_fg_of_mvPolynomial
    (R := B) (A := A) (n := d) f hf
  obtain ⟨a, rs, ha, hrs, hlen', hgen', hreg'⟩ :=
    Ideal.exists_principal_relations_of_regular_reduction
      (R := MvPolynomial (Fin d) B) (U := Localization.AtPrime P ⧸ J)
      P (RingHom.ker f) hfg ws hgen (Ideal.Quotient.mk J) hreg
  exact ⟨a, rs, ha, hlen'.trans hlen, hrs, hgen', hreg',
    f.exists_principal_presentation_equiv hf a rs hgen'⟩

end ThreeAdicPlan.PDivisibleSystem
