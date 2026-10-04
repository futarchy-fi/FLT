/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionGeometricFibre
public import FLT.GroupScheme.FiniteAlgebraPrincipalComponents
public import FLT.GroupScheme.FiniteHopfComponentRegularPresentation
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Regular local factors of the actual geometric division fibre -/

@[expose] public noncomputable section

open scoped TensorProduct
open FiniteAlgebra MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K Ω : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
  {p height : ℕ} [Fact p.Prime] [CharP Ω p] (X : PDivisibleSystem R K p height)

/-- The actual division fibre is a finite product of quotients of polynomial local rings by
regular sequences; its factor maps use the original comultiplication and kernel inclusion. -/
theorem exists_geometric_division_regular_components (m n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[R] Ω) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing Ω := x.toRingHom.toAlgebra
    let D := Ω ⊗[R] (X.level m).CoordinateRing
    let : IsArtinianRing D := IsArtinianRing.of_finite Ω D
    ∃ (y : (X.level (m + n)).CoordinateRing →ₐ[R] Ω),
      y.comp (X.reduction (Nat.le_add_left n m)).toAlgHom = x ∧
      ∃ e : Ω ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing ≃ₐ[Ω]
          Π j : ComponentIndex D, Component D j,
        (∀ a j, e (1 ⊗ₜ[(X.level n).CoordinateRing] a) j = Ideal.Quotient.mk _
          (Algebra.TensorProduct.map y (X.inclusion (Nat.le_add_right m n)).toAlgHom
            (Coalgebra.comul a))) ∧
        Ideal.span (Set.range (FiniteAlgebra.componentIdempotent D)) = ⊤ ∧
        ∀ j : ComponentIndex D,
          ∃ (d : ℕ) (rs : List (Localization.AtPrime
              (rationalPointIdeal (fun _ : Fin d ↦ (0 : Ω))))),
            rs.length = d ∧
            RingTheory.Sequence.IsRegular
              (Localization.AtPrime (rationalPointIdeal (fun _ : Fin d ↦ (0 : Ω)))) rs ∧
            Nonempty (((Localization.AtPrime (rationalPointIdeal (fun _ : Fin d ↦ (0 : Ω)))) ⧸
              Ideal.ofList rs) ≃ₐ[Ω] Component D j) := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing Ω := x.toRingHom.toAlgebra
  let D := Ω ⊗[R] (X.level m).CoordinateRing
  let : IsArtinianRing D := IsArtinianRing.of_finite Ω D
  obtain ⟨y, hy, e, he⟩ := X.exists_geometric_division_fibre_equiv m n x
  refine ⟨y, hy, e.trans (componentEquiv D Ω), ?_,
    span_componentIdempotents_eq_top D, ?_⟩
  · intro a j
    change Ideal.Quotient.mk _ (e (1 ⊗ₜ[(X.level n).CoordinateRing] a)) = _
    rw [he]
    rfl
  · intro j
    exact HopfAlgebra.exists_component_regular_presentation (k := Ω) (A := D) p j

end ThreeAdicPlan.PDivisibleSystem
