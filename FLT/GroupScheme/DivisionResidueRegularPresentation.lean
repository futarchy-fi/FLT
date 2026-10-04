/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionResidueFibreComparison
public import FLT.GroupScheme.HopfGeometricPointDescent

/-! # Regular relations for the actual residue-field division fibre -/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K k Ω : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field k] [Algebra R k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω]
  {p height : ℕ} [Fact p.Prime] [CharP Ω p]
  (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- A presentation of the original residue fibre has regular relations at every
contracted geometric point. The geometric Hopf comparison is constructed, not assumed. -/
theorem exists_residue_division_regular_relations
    (x : (X.level n).CoordinateRing →ₐ[R] k) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
    ∀ {d : ℕ} (f : MvPolynomial (Fin d) k →ₐ[k]
        k ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing),
      Function.Surjective f →
      ∀ y : (k ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing) →ₐ[k] Ω,
      ∃ rs : List (GeometricPointSource k Ω (fun i ↦ y (f (MvPolynomial.X i)))), rs.length = d ∧
        Ideal.ofList rs = (RingHom.ker f).map
          (algebraMap _ (GeometricPointSource k Ω (fun i ↦ y (f (MvPolynomial.X i))))) ∧
        RingTheory.Sequence.IsRegular
          (GeometricPointSource k Ω (fun i ↦ y (f (MvPolynomial.X i)))) rs := by
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
  dsimp only
  intro d f hf y
  have : IsArtinianRing (Ω ⊗[R] (X.level m).CoordinateRing) :=
    IsArtinianRing.of_finite Ω _
  obtain ⟨e⟩ := X.nonempty_residue_division_fibre_comparison (Ω := Ω) m n x
  exact HopfAlgebra.exists_original_relations_at_fibre_point p f hf e y

end ThreeAdicPlan.PDivisibleSystem
