/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalConnectedKernel
public import FLT.GroupScheme.RationalIdentityMapFaithfullyFlat
public import FLT.GroupScheme.LocalKernelRank
public import FLT.GroupScheme.RaynaudAugmentationRank
public import Mathlib.GroupTheory.Coset.Card

/-! # A common height for the actual connected level tower -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The rank of every connected level divides the rank of the original level. -/
theorem rationalConnected_rank_dvd (n : ℕ) :
    Module.finrank O (X.rationalConnectedLevel n).CoordinateRing ∣ p ^ (n * height) := by
  rw [← X.rank n, FF.coordinate_finrank, FF.coordinate_finrank]
  exact AddSubgroup.card_dvd_of_injective
    (genericHom (X.rationalConnectedEmbedding n)).toAddMonoidHom
    (X.level n).rationalIdentityComponentInclusion_genericHom_injective

/-- Connected coordinate ranks multiply across the original exact sequence. -/
theorem rationalConnected_rank_add (m n : ℕ) :
    Module.finrank O (X.rationalConnectedLevel (m + n)).CoordinateRing =
      Module.finrank O (X.rationalConnectedLevel m).CoordinateRing *
        Module.finrank O (X.rationalConnectedLevel n).CoordinateRing := by
  let : IsLocalRing (X.rationalConnectedLevel n).CoordinateRing :=
    (X.level n).rationalComponentAlgebra_isLocalRing _
  exact coordinate_finrank_of_local_kernel
    (X.rationalConnectedInclusion (Nat.le_add_right m n))
    (X.rationalConnectedReduction (Nat.le_add_left n m))
    (X.rationalConnectedInclusion_closed _) (X.rationalConnectedReduction_faithfullyFlat _)
    (X.rationalConnected_kernel m n)

/-- Level zero of the connected system has rank one. -/
theorem rationalConnected_rank_zero :
    Module.finrank O (X.rationalConnectedLevel 0).CoordinateRing = 1 := by
  have h := X.rationalConnected_rank_dvd 0
  simpa using h

/-- All connected ranks are powers of the first connected rank. -/
theorem rationalConnected_rank_pow (n : ℕ) :
    Module.finrank O (X.rationalConnectedLevel n).CoordinateRing =
      (Module.finrank O (X.rationalConnectedLevel 1).CoordinateRing) ^ n := by
  induction n with
  | zero => simpa using X.rationalConnected_rank_zero
  | succ n ih => rw [X.rationalConnected_rank_add n 1, ih, pow_succ]

/-- The first connected rank is a power of the original prime, bounded by the ambient height. -/
theorem exists_rationalConnectedHeight : ∃ h ≤ height,
    Module.finrank O (X.rationalConnectedLevel 1).CoordinateRing = p ^ h := by
  apply (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
  simpa using X.rationalConnected_rank_dvd 1

/-- The height is selected from a proved prime-power rank formula. -/
def rationalConnectedHeight : ℕ := X.exists_rationalConnectedHeight.choose

/-- The connected height is at most the original height. -/
theorem rationalConnectedHeight_le : X.rationalConnectedHeight ≤ height :=
  X.exists_rationalConnectedHeight.choose_spec.1

/-- Every actual connected level has the common connected-height rank. -/
theorem rationalConnected_rank (n : ℕ) :
    Module.finrank O (X.rationalConnectedLevel n).CoordinateRing =
      p ^ (n * X.rationalConnectedHeight) := by
  rw [X.rationalConnected_rank_pow, X.exists_rationalConnectedHeight.choose_spec.2,
    ← pow_mul, Nat.mul_comm]
  rfl
end ThreeAdicPlan.PDivisibleSystem
