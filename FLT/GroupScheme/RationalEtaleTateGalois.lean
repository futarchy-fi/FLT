/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleTateModule

/-! # Original Galois actions on the connected–étale inverse-limit sequence -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The quotient inverse limit retains the original coordinatewise Galois action. -/
instance rationalEtaleTateGaloisAction :
    DistribMulAction (Field.absoluteGaloisGroup K) X.rationalEtaleTateSequences where
  smul g x := ⟨fun n ↦ g • x.val n, by
    intro m n h
    rw [map_smul, x.property h]⟩
  one_smul x := by apply Subtype.ext; funext n; exact one_smul _ _
  mul_smul g h x := by apply Subtype.ext; funext n; exact mul_smul _ _ _
  smul_zero g := by apply Subtype.ext; funext n; exact smul_zero _
  smul_add g x y := by apply Subtype.ext; funext n; exact smul_add _ _ _

/-- The actual quotient projection is equivariant for the original Galois action. -/
theorem rationalEtaleTateProjection_galois (g : Field.absoluteGaloisGroup K)
    (x : X.tateSequences) :
    X.rationalEtaleTateProjectionLinear (g • x) = g • X.rationalEtaleTateProjectionLinear x := by
  apply Subtype.ext
  funext n
  exact map_smul (genericHom (X.rationalEtaleProjection n)) g (X.tateEval n x)

/-- The actual connected inclusion is equivariant for the original Galois action. -/
theorem rationalConnectedTateInclusion_galois (g : Field.absoluteGaloisGroup K)
    (x : X.rationalConnectedSystem.tateSequences) :
    X.rationalConnectedTateInclusion (g • x) = g • X.rationalConnectedTateInclusion x := by
  apply X.tate_ext
  intro n
  exact map_smul (genericHom (X.rationalConnectedEmbedding n)) g
    (X.rationalConnectedSystem.tateEval n x)

/-- Galois commutes with the p-adic scalars on the actual quotient inverse limit. -/
instance rationalEtaleTateSmulCommClass :
    SMulCommClass (Field.absoluteGaloisGroup K) ℤ_[p] X.rationalEtaleTateSequences where
  smul_comm g a x := by
    apply Subtype.ext
    funext n
    change g • (PadicInt.toZModPow n a • x.val n) =
      PadicInt.toZModPow n a • (g • x.val n)
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a),
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact smul_comm g _ _
end ThreeAdicPlan.PDivisibleSystem
