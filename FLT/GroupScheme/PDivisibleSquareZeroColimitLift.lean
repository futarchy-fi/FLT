/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointMultiplication
public import FLT.GroupScheme.SquareZeroLiftNaturality

/-! # Canonical square-zero multiplication lifts on the original point colimit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  (q : B →ₐ[R] C) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
  (N : ℕ) (hN : ∀ b ∈ RingHom.ker q, N • b = 0)

/-- The canonical multiplication lift at an original finite level. -/
def squareZeroLevelLift (n : ℕ) (x : (X.level n).CoordinateRing →ₐ[R] C) :
    (X.level n).CoordinateRing →ₐ[R] B := by
  let : Module.Free R (X.level n).CoordinateRing := Module.free_of_flat_of_isLocalRing
  exact HopfAlgebra.squareZeroPointLift q hq hJ N hN x

/-- The canonical finite lift commutes with all original inclusions. -/
theorem squareZeroLevelLift_inclusion {m n : ℕ} (h : m ≤ n)
    (x : (X.level m).CoordinateRing →ₐ[R] C) :
    (X.squareZeroLevelLift q hq hJ N hN m x).comp (X.inclusion h).toAlgHom =
      X.squareZeroLevelLift q hq hJ N hN n (x.comp (X.inclusion h).toAlgHom) := by
  let (i : ℕ) : Module.Free R (X.level i).CoordinateRing := Module.free_of_flat_of_isLocalRing
  exact HopfAlgebra.squareZeroPointLift_precomp q hq hJ N hN x (X.inclusion h)

/-- Inclusion compatibility descends the canonical lift to the actual point colimit. -/
def squareZeroColimitLift : X.PointColimit C → X.PointColimit B :=
  DirectLimit.map _ _ (X.squareZeroLevelLift q hq hJ N hN)
    (fun _ _ h x ↦ (X.squareZeroLevelLift_inclusion q hq hJ N hN h x))

/-- Reduction of the canonical lift is original multiplication by N. -/
theorem squareZeroColimitLift_reduction (x : X.PointColimit C) :
    X.pointColimitMap q (X.squareZeroColimitLift q hq hJ N hN x) =
      X.pointColimitMul N x := by
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨n, x⟩ := x
    let : Module.Free R (X.level n).CoordinateRing := Module.free_of_flat_of_isLocalRing
    apply congrArg (X.pointColimitMk n)
    exact (HopfAlgebra.squareZeroPointLift_reduction q hq hJ N hN x).trans
      ((X.level n).point_comp_multiply N x).symm

/-- Lifting the reduction of a point also gives original multiplication by N. -/
theorem squareZeroColimitLift_map (x : X.PointColimit B) :
    X.squareZeroColimitLift q hq hJ N hN (X.pointColimitMap q x) =
      X.pointColimitMul N x := by
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨n, x⟩ := x
    let : Module.Free R (X.level n).CoordinateRing := Module.free_of_flat_of_isLocalRing
    apply congrArg (X.pointColimitMk n)
    exact (HopfAlgebra.squareZeroPointLift_eq_of_algHom q hq hJ N hN _ x rfl).trans
      ((X.level n).point_comp_multiply N x).symm

/-- The canonical lift commutes with multiplication, hence with Tate transitions. -/
theorem squareZeroColimitLift_mul (M : ℕ) (x : X.PointColimit C) :
    X.squareZeroColimitLift q hq hJ N hN (X.pointColimitMul M x) =
      X.pointColimitMul M (X.squareZeroColimitLift q hq hJ N hN x) := by
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨n, x⟩ := x
    let : Module.Free R (X.level n).CoordinateRing := Module.free_of_flat_of_isLocalRing
    apply congrArg (X.pointColimitMk n)
    exact (HopfAlgebra.squareZeroPointLift_precomp q hq hJ N hN x
      ((X.level n).multiply M)).symm

end ThreeAdicPlan.PDivisibleSystem
