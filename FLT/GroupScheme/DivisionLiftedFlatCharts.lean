/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionRelativeCICover
public import FLT.GroupScheme.LiftedPrincipalSquareCover

/-! # Flat lifted charts for the actual division pullback -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R C] [Algebra B C]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- Construct the original division charts and their lifted equations internally.
The lifted product is faithfully flat over the thickened base, and every chart reduces
to the specified principal open of the original division pullback. -/
theorem exists_division_lifted_flat_charts
    (hq : Function.Surjective (algebraMap B C)) {k : ℕ}
    (hn : RingHom.ker (algebraMap B C) ^ k = ⊥)
    (hC : IsNilpotent (p : C)) (x : (X.level n).CoordinateRing →ₐ[R] C) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing C := x.toRingHom.toAlgebra
    let A := C ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) C →ₐ[C] A), Function.Surjective f ∧
      ∃ (t : Finset (MvPolynomial (Fin d) C ⧸ RingHom.ker f))
        (a : t → MvPolynomial (Fin d) C)
        (P : ∀ i, Algebra.Presentation C (Localization.Away (f (a i)))
          (Fin (d + 1)) (Fin (d + 1)))
        (g : t → Fin (d + 1) → MvPolynomial (Fin (d + 1)) B),
        (∀ i j, MvPolynomial.map (algebraMap B C) (g i j) = (P i).relation j) ∧
        Ideal.span (Set.range fun i ↦ f (a i)) = ⊤ ∧
        Module.FaithfullyFlat B
          (∀ i, MvPolynomial (Fin (d + 1)) B ⧸ Ideal.span (Set.range (g i))) ∧
        ∀ i, Nonempty (((MvPolynomial (Fin (d + 1)) B ⧸ Ideal.span (Set.range (g i)))
          ⊗[B] C) ≃ₐ[B] Localization.Away (f (a i))) := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing C := x.toRingHom.toAlgebra
  let : IsScalarTower R (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    IsScalarTower.of_algHom (X.reduction (Nat.le_add_left n m)).toAlgHom
  have : Module.Finite (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : Module.FaithfullyFlat (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    X.faithfullyFlat (Nat.le_add_left n m)
  let A := C ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
  have : IsScalarTower B C A := inferInstance
  obtain ⟨d, f, hf, t, a, rs, hspan, hcharts⟩ := X.exists_division_relative_ci_cover m n hC x
  obtain ⟨P, g, hg, hflat, he⟩ := Algebra.Presentation.exists_faithfullyFlat_liftedPrincipalCover
    (B := B) f hf a rs (fun i ↦ (hcharts i).1) (fun i ↦ (hcharts i).2.2.1) hspan hq hn
  exact ⟨d, f, hf, t, a, P, g, hg, hspan, hflat, he⟩

end ThreeAdicPlan.PDivisibleSystem
