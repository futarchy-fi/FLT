/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionLiftedReductionPoint
public import FLT.GroupScheme.PDivisibleInfinitesimalFlatCover
public import FLT.GroupScheme.PDivisibleSquareZeroLifting

/-! # Actual local inclusion lifts on the constructed faithfully flat cover -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- A point on the original level lifts along its specified inclusion after a constructed
faithfully flat base change. The lift is an actual point, not just a reduced division point. -/
theorem exists_local_inclusion_point_lift
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (hC : IsNilpotent (p : C)) (m n : ℕ)
    (hm : ∀ b : RingHom.ker (algebraMap B C), p ^ m • b = 0)
    (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra R D)
      (_ : IsScalarTower R B D), Module.FaithfullyFlat B D ∧
      ∃ y : (X.level (m + n)).CoordinateRing →ₐ[R] D,
        (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
          (Algebra.TensorProduct.includeRight.restrictScalars R).comp
            (x.comp (X.inclusion (Nat.le_add_left n m)).toAlgHom) := by
  obtain ⟨D, _, _, _, _, hflat, z, hz⟩ :=
    X.exists_division_point_on_lifted_cover hq hJ hC m n x
  let := hflat
  let q := coverPointReduction (R := R) (B := B) (C := C) (D := D)
  have hq' : Function.Surjective q := Algebra.TensorProduct.includeLeft_surjective B D hq
  have hJ' : RingHom.ker q ^ 2 = ⊥ := Algebra.squareZero_coverReduction B C D hq hJ
  have hm' (b : D) (hb : b ∈ RingHom.ker q) : p ^ (m + n - n) • b = 0 := by
    simpa using congrArg Subtype.val
      (Algebra.nsmul_coverReduction_kernel B C D (p ^ m) hm ⟨b, hb⟩)
  obtain ⟨y, hy⟩ := X.exists_reduction_inclusion_point_lift q hq' hJ'
    (Nat.le_add_left n m) hm' z
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, hflat, y, ?_⟩
  rw [hy, hz, AlgHom.comp_assoc]

end ThreeAdicPlan.PDivisibleSystem
