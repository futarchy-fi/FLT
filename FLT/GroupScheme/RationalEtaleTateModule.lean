/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleTateSurjective

/-! # The original connected–étale exact sequence of p-adic inverse-limit modules -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual annihilator supplies the residue action at each quotient level. -/
instance rationalEtaleLevelZmodModule (n : ℕ) :
    Module (ZMod (p ^ n)) (X.rationalEtaleLevel n).Points :=
  AddCommGroup.zmodModule (X.rationalEtaleLevel_killed n)

/-- The p-adic action is the original residue action at each quotient level. -/
instance rationalEtaleLevelPadicModule (n : ℕ) : Module ℤ_[p] (X.rationalEtaleLevel n).Points :=
  Module.compHom (X.rationalEtaleLevel n).Points (PadicInt.toZModPow n)

/-- Reductions on the actual quotient points are p-adic linear. -/
theorem rationalEtaleReduction_padic_smul {m n : ℕ} (h : m ≤ n) (a : ℤ_[p])
    (x : (X.rationalEtaleLevel n).Points) :
    genericHom (X.rationalEtaleReduction h) (a • x) =
      a • genericHom (X.rationalEtaleReduction h) x := by
  let k := (PadicInt.toZModPow n a).val
  have hn : PadicInt.toZModPow n a = (k : ZMod (p ^ n)) := (ZMod.natCast_zmod_val _).symm
  have hm : PadicInt.toZModPow m a = (k : ZMod (p ^ m)) := by
    have he := congrArg (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) hn
    rw [map_natCast] at he
    change ((ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp
      (PadicInt.toZModPow n)) a = _ at he
    rw [PadicInt.zmod_cast_comp_toZModPow m n h] at he
    exact he
  change genericHom (X.rationalEtaleReduction h) (PadicInt.toZModPow n a • x) =
    PadicInt.toZModPow m a • genericHom (X.rationalEtaleReduction h) x
  rw [hn, hm, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/-- Coherent quotient sequences form a submodule of the original product. -/
def rationalEtaleTateSubmodule : Submodule ℤ_[p] (∀ n, (X.rationalEtaleLevel n).Points) where
  __ := X.rationalEtaleTateSequences
  smul_mem' a x hx := by
    intro m n h
    change genericHom (X.rationalEtaleReduction h) (a • x n) = a • x m
    rw [X.rationalEtaleReduction_padic_smul, hx h]

/-- The actual inverse limit carries its p-adic module structure. -/
instance rationalEtaleTatePadicModule : Module ℤ_[p] X.rationalEtaleTateSequences :=
  inferInstanceAs (Module ℤ_[p] X.rationalEtaleTateSubmodule)

/-- The original inverse-limit projection is linear over the p-adic integers. -/
def rationalEtaleTateProjectionLinear : X.tateSequences →ₗ[ℤ_[p]] X.rationalEtaleTateSequences where
  __ := X.rationalEtaleTateProjection
  map_smul' a x := by
    apply Subtype.ext
    funext n
    change genericHom (X.rationalEtaleProjection n) (PadicInt.toZModPow n a • X.tateEval n x) =
      PadicInt.toZModPow n a • genericHom (X.rationalEtaleProjection n) (X.tateEval n x)
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul, map_nsmul]

/-- Surjectivity holds for the original p-adic linear projection. -/
theorem rationalEtaleTateProjectionLinear_surjective :
    Function.Surjective X.rationalEtaleTateProjectionLinear :=
  X.rationalEtaleTateProjection_surjective

/-- The kernel is precisely the image of the original connected p-adic Tate inclusion. -/
theorem rationalEtaleTateProjectionLinear_exact :
    X.rationalEtaleTateProjectionLinear.ker = X.rationalConnectedTateInclusion.range := by
  ext x
  exact X.rationalEtaleTateProjection_exact x
end ThreeAdicPlan.PDivisibleSystem
