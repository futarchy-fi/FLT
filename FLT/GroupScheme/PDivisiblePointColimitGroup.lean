/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointMultiplication
public import FLT.GroupScheme.HopfTestAlgebraPoints
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Group.TransferInstance

/-! # Convolution group structure on the original point colimit -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open WithConv
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The finite-stage group is the original Hopf convolution group. -/
local instance levelPointGroup (n : ℕ) : CommGroup ((X.level n).CoordinateRing →ₐ[R] B) := by
  letI : CommGroup (WithConv ((X.level n).CoordinateRing →ₐ[R] B)) :=
    { HopfAlgebra.testAlgebraPointGroup R (X.level n).CoordinateRing B with
      mul_comm := mul_comm }
  exact (WithConv.equiv _).symm.commGroup

/-- Original closed inclusions preserve the convolution group law. -/
def pointInclusionHom {m n : ℕ} (h : m ≤ n) :
    ((X.level m).CoordinateRing →ₐ[R] B) →* ((X.level n).CoordinateRing →ₐ[R] B) where
  toFun := X.pointInclusion h
  map_one' := by
    ext a
    exact congrArg (algebraMap R B) (CoalgHomClass.counit_comp_apply (X.inclusion h) a)
  map_mul' x y := AlgHom.convMul_comp_bialgHom_distrib (toConv x) (toConv y) _

local instance pointHomDirectedSystem :
    DirectedSystem (fun n ↦ (X.level n).CoordinateRing →ₐ[R] B)
      (fun _ _ h ↦ X.pointInclusionHom (B := B) h) :=
  X.pointDirectedSystem

/-- The original set colimit carries its finite-stage convolution group law. -/
instance pointColimitCommGroup : CommGroup (X.PointColimit B) :=
  inferInstanceAs (CommGroup (DirectLimit
    (fun n ↦ (X.level n).CoordinateRing →ₐ[R] B) (fun _ _ h ↦ X.pointInclusionHom (B := B) h)))

/-- The canonical inclusion of a finite stage is a group homomorphism. -/
def pointColimitMkHom (n : ℕ) :
    ((X.level n).CoordinateRing →ₐ[R] B) →* X.PointColimit B where
  toFun := X.pointColimitMk n
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ X.pointInclusionHom (B := B) h) n).symm
  map_mul' _ _ := (DirectLimit.mul_def (f := fun _ _ h ↦ X.pointInclusionHom (B := B) h) ..).symm

/-- Coefficient maps preserve the identity point. -/
theorem pointColimitMap_one (q : B →ₐ[R] C) : X.pointColimitMap q 1 = 1 := by
  rw [← (X.pointColimitMkHom (B := B) 0).map_one,
    ← (X.pointColimitMkHom (B := C) 0).map_one]
  change X.pointColimitMk 0 (q.comp _) = X.pointColimitMk 0 _
  congr 1
  ext a
  exact q.commutes _

/-- Coefficient maps preserve the finite-stage convolution product. -/
theorem pointColimitMap_mul (q : B →ₐ[R] C) (x y : X.PointColimit B) :
    X.pointColimitMap q (x * y) = X.pointColimitMap q x * X.pointColimitMap q y := by
  induction x, y using DirectLimit.induction₂ (fun _ _ h ↦ X.pointInclusionHom (B := B) h) with
  | ih n x y =>
    change X.pointColimitMap q
      (X.pointColimitMkHom n x * X.pointColimitMkHom n y) = _
    rw [← map_mul]
    change X.pointColimitMkHom n (q.comp (x * y)) =
      X.pointColimitMkHom n (q.comp x) * X.pointColimitMkHom n (q.comp y)
    rw [← map_mul]
    exact congrArg (X.pointColimitMkHom n)
      (AlgHom.comp_convMul_distrib q (toConv x) (toConv y))

/-- The original coefficient action, now as a group homomorphism. -/
def pointColimitMapHom (q : B →ₐ[R] C) : X.PointColimit B →* X.PointColimit C where
  toFun := X.pointColimitMap q
  map_one' := X.pointColimitMap_one q
  map_mul' := X.pointColimitMap_mul q

/-- The previously constructed multiplication agrees with group powers. -/
theorem pointColimitMul_eq_pow (N : ℕ) (x : X.PointColimit B) :
    X.pointColimitMul N x = x ^ N := by
  induction x using DirectLimit.induction with
  | _ n x =>
    rw [show (⟦⟨n, x⟩⟧ : X.PointColimit B) = X.pointColimitMk n x from rfl,
      X.pointColimitMul_mk, (X.level n).point_comp_multiply]
    exact (X.pointColimitMkHom n).map_pow x N

end ThreeAdicPlan.PDivisibleSystem
