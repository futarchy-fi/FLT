/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleLevelTower
public import FLT.GroupScheme.RationalConnectedRanks

/-! # The complementary height of the original étale quotient levels -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- The original coordinate rank is the product of the connected and étale ranks. -/
theorem FF.rationalComponent_rank_mul (X : FF
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) :
    Module.finrank O X.rationalIdentityComponent.CoordinateRing *
        Module.finrank O X.rationalComponentQuotient.CoordinateRing =
      Module.finrank O X.CoordinateRing := by
  rw [FF.coordinate_finrank, FF.coordinate_finrank, FF.coordinate_finrank]
  have hc : Nat.card X.rationalComponentQuotient.Points =
      (genericHom X.rationalIdentityComponentInclusion).toAddMonoidHom.range.index :=
    X.exists_rationalComponentQuotient.choose_spec.choose_spec.2.2
  have hi := Nat.card_congr (Equiv.ofInjective
    (genericHom X.rationalIdentityComponentInclusion).toAddMonoidHom
    X.rationalIdentityComponentInclusion_genericHom_injective)
  rw [hc, hi]
  exact (genericHom X.rationalIdentityComponentInclusion).toAddMonoidHom.range.card_mul_index

namespace PDivisibleSystem
variable {height : ℕ}
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The complementary height of the original finite étale quotient levels. -/
def rationalEtaleHeight : ℕ := height - X.rationalConnectedHeight

/-- The connected and étale heights sum to the original height. -/
theorem rationalConnectedHeight_add_etaleHeight :
    X.rationalConnectedHeight + X.rationalEtaleHeight = height :=
  Nat.add_sub_of_le X.rationalConnectedHeight_le

/-- The actual quotient levels have the complementary-height rank formula. -/
theorem rationalEtale_rank (n : ℕ) :
    Module.finrank O (X.rationalEtaleLevel n).CoordinateRing = p ^ (n * X.rationalEtaleHeight) := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos (n * X.rationalConnectedHeight))
  have hr := (X.level n).rationalComponent_rank_mul
  change Module.finrank O (X.rationalConnectedLevel n).CoordinateRing *
    Module.finrank O (X.rationalEtaleLevel n).CoordinateRing =
      Module.finrank O (X.level n).CoordinateRing at hr
  rw [X.rationalConnected_rank, X.rank] at hr
  rw [hr, ← pow_add, ← Nat.mul_add, X.rationalConnectedHeight_add_etaleHeight]
end PDivisibleSystem
end ThreeAdicPlan
