/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointColimit
public import FLT.GroupScheme.FiniteFlatSquareZeroLifting

/-! # Multiplication on the original point colimit -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K]

omit [IsLocalRing R] in
/-- Original multiplication is natural in every model morphism. -/
theorem ModelHom.multiply_natural {Y Z : FF R K} (f : ModelHom Y Z) (N : ℕ) :
    (Y.multiply N).comp f = f.comp (Z.multiply N) := by
  apply genericHom_injective
  ext x
  simp only [genericHom_comp, FF.genericHom_multiply, map_nsmul]

namespace PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)
  {B C : Type} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- Multiplication by N, defined on the original finite stages and their given inclusions. -/
def pointColimitMul (N : ℕ) : X.PointColimit B → X.PointColimit B :=
  DirectLimit.map _ _ (fun n x ↦ x.comp ((X.level n).multiply N).toAlgHom) (by
    intro i j h x
    change (x.comp ((X.level i).multiply N).toAlgHom).comp (X.inclusion h).toAlgHom =
      (x.comp (X.inclusion h).toAlgHom).comp ((X.level j).multiply N).toAlgHom
    ext a
    exact congrArg x (DFunLike.congr_fun ((X.inclusion h).multiply_natural N) a))

/-- Its value is the specified multiplication morphism on every original representative. -/
theorem pointColimitMul_mk (N n : ℕ) (x : (X.level n).CoordinateRing →ₐ[R] B) :
    X.pointColimitMul N (X.pointColimitMk n x) =
      X.pointColimitMk n (x.comp ((X.level n).multiply N).toAlgHom) := rfl

/-- Multiplication commutes with every coefficient map. -/
theorem pointColimitMul_map (N : ℕ) (q : B →ₐ[R] C) (x : X.PointColimit B) :
    X.pointColimitMul N (X.pointColimitMap q x) =
      X.pointColimitMap q (X.pointColimitMul N x) := by
  induction x using Quotient.ind with | _ x => rfl

/-- Multiplication by one is the identity. -/
theorem pointColimitMul_one (x : X.PointColimit B) : X.pointColimitMul 1 x = x := by
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨n, x⟩ := x
    change X.pointColimitMk n (x.comp ((X.level n).multiply 1).toAlgHom) = _
    have he : (X.level n).multiply 1 = BialgHom.id R _ := by
      simp [FF.multiply]
    rw [he]
    rfl

/-- Composition of original multiplication maps multiplies the natural scalars. -/
theorem pointColimitMul_mul (M N : ℕ) (x : X.PointColimit B) :
    X.pointColimitMul M (X.pointColimitMul N x) = X.pointColimitMul (M * N) x := by
  induction x using Quotient.ind with
  | _ x =>
    obtain ⟨n, x⟩ := x
    have he : ((X.level n).multiply N).comp ((X.level n).multiply M) =
        (X.level n).multiply (M * N) := by
      apply genericHom_injective
      ext z
      simp only [genericHom_comp, FF.genericHom_multiply, mul_smul]
    change X.pointColimitMk n
      ((x.comp ((X.level n).multiply N).toAlgHom).comp ((X.level n).multiply M).toAlgHom) = _
    apply congrArg (X.pointColimitMk n)
    ext a
    exact congrArg x (DFunLike.congr_fun he a)

/-- Iterated p multiplication is the actual p-power multiplication. -/
theorem pointColimitMul_iterate (n : ℕ) (x : X.PointColimit B) :
    (X.pointColimitMul p)^[n] x = X.pointColimitMul (p ^ n) x := by
  induction n with
  | zero => exact (X.pointColimitMul_one x).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, X.pointColimitMul_mul, pow_succ']

end PDivisibleSystem
end ThreeAdicPlan
