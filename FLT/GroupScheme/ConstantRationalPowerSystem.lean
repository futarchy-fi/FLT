/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalPowerLevels
public import FLT.GroupScheme.RationalIntegralKernel
public import FLT.GroupScheme.IntegralKernelEquations
public import FLT.GroupScheme.PDivisibleSystem

/-! # The constant height-one p-divisible system at an odd rational prime -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ConstantRationalPower
open ConstantPower
variable (p : ℕ) [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Integral inclusions preserve identities. -/
theorem inclusion_refl (n : ℕ) : inclusion p (le_refl n) = BialgHom.id O _ := by
  apply genericHom_injective
  ext x
  obtain ⟨a, rfl⟩ := (points p n).surjective x
  rw [inclusion_points, embed_refl, genericHom_id]

/-- Integral reductions preserve identities. -/
theorem reduction_refl (n : ℕ) : reduction p (le_refl n) = BialgHom.id O _ := by
  apply genericHom_injective
  ext x
  obtain ⟨a, rfl⟩ := (points p n).surjective x
  rw [reduction_points, reduce_refl, genericHom_id]

/-- Integral inclusions compose. -/
theorem inclusion_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (inclusion p h).comp (inclusion p k) = inclusion p (h.trans k) := by
  apply genericHom_injective
  ext x
  obtain ⟨a, rfl⟩ := (points p l).surjective x
  simp only [genericHom_comp, inclusion_points, embed_comp]

/-- Integral reductions compose. -/
theorem reduction_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (reduction p k).comp (reduction p h) = reduction p (h.trans k) := by
  apply genericHom_injective
  ext x
  obtain ⟨a, rfl⟩ := (points p n).surjective x
  simp only [genericHom_comp, reduction_points, reduce_comp]

/-- The lower multiplication is the prescribed inclusion followed by reduction. -/
theorem inclusion_reduction {m n : ℕ} (h : m ≤ n) :
    (inclusion p h).comp (reduction p h) = (level p m).multiply (p ^ (n - m)) := by
  apply genericHom_injective
  ext x
  obtain ⟨a, rfl⟩ := (points p m).surjective x
  simp only [genericHom_comp, inclusion_points,
    reduction_points, reduce_embed, FF.genericHom_multiply, map_nsmul]

/-- The higher multiplication is reduction followed by inclusion. -/
theorem reduction_inclusion {m n : ℕ} (h : m ≤ n) :
    (reduction p h).comp (inclusion p h) = (level p n).multiply (p ^ (n - m)) := by
  apply genericHom_injective
  ext x
  obtain ⟨a, rfl⟩ := (points p n).surjective x
  simp only [genericHom_comp, inclusion_points,
    reduction_points, embed_reduce, FF.genericHom_multiply, map_nsmul]

/-- Closedness of these actual integral inclusions. -/
theorem closed (hp : 2 < p) {m n : ℕ} (h : m ≤ n) : Function.Surjective (inclusion p h) :=
  ModelHom.closed_of_rational_power p hp (killedByPower p m) _ (inclusion_injective p h)

/-- Faithful flatness of these actual integral reductions. -/
theorem faithfullyFlat (hp : 2 < p) {m n : ℕ} (h : m ≤ n) :
    (reduction p h).toAlgHom.toRingHom.FaithfullyFlat :=
  ModelHom.faithfullyFlat_of_rational_power p hp (killedByPower p m) _
    (reduction_surjective p h)

/-- Exactness holds on integral coordinate ideals, not just generic points. -/
theorem kernel (hp : 2 < p) (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (reduction p (Nat.le_add_left n m)) =
      RingHom.ker (inclusion p (Nat.le_add_right m n)).toAlgHom.toRingHom := by
  rw [ModelHom.ker_eq_closureIdeal _ (inclusion_injective p _) (closed p hp _)]
  exact ModelHom.augmentationIdeal_eq_closure p hp (killedByPower p n) _ _
    (reduction_surjective p _) (point_exact p m n)

/-- The constant etale system, with every defining property proved for its original maps.
The odd-prime bound is used only by the integral exactness API. -/
def system (hp : 2 < p) : PDivisibleSystem O K p 1 where
  level := level p
  inclusion := inclusion p
  reduction := reduction p
  inclusion_refl := inclusion_refl p
  reduction_refl := reduction_refl p
  inclusion_comp := inclusion_comp p
  reduction_comp := reduction_comp p
  closed := closed p hp
  faithfullyFlat := faithfullyFlat p hp
  kernel := kernel p hp
  inclusion_reduction := inclusion_reduction p
  reduction_inclusion := reduction_inclusion p
  killed := killed p
  rank n := by simpa only [Nat.mul_one] using rank p n

end ThreeAdicPlan.ConstantRationalPower
