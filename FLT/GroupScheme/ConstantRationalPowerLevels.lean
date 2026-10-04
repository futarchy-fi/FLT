/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantGroupMorphisms
public import FLT.GroupScheme.ConstantPowerCoherence
public import FLT.GroupScheme.RationalIntegralTransition

/-! # Constant cyclic levels over the original rational-place base -/

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

/-- The actual constant finite-flat model of the integer residues. -/
abbrev level (n : ℕ) : FF O K := constantGroupModel O K (Residue p n)

/-- The prescribed residue-to-geometric-point equivalence. -/
abbrev points (n : ℕ) : Residue p n ≃+ (level p n).Points := constantGroupPointEquiv O K _

/-- Each level is etale over the integral base, even though its order is not a unit. -/
instance levelEtale (n : ℕ) : Algebra.Etale O (level p n).CoordinateRing :=
  Algebra.Etale.of_equiv (constantGroupCoordinates O K (Residue p n)).symm

/-- The closed transition will be the extension of residue multiplication. -/
def inclusion {m n : ℕ} (h : m ≤ n) : ModelHom (level p m) (level p n) :=
  constantGroupHom O K (embed p h).toAddMonoidHom

/-- The quotient transition is the extension of the residue reduction. -/
def reduction {m n : ℕ} (h : m ≤ n) : ModelHom (level p n) (level p m) :=
  constantGroupHom O K (reduce p h).toAddMonoidHom

@[simp] theorem inclusion_points {m n : ℕ} (h : m ≤ n) (a : Residue p m) :
    genericHom (inclusion p h) (points p m a) = points p n (embed p h a) := by
  rw [inclusion, genericHom_constantGroupHom]
  exact constantGroupGenericHom_point O K (embed p h).toAddMonoidHom a

@[simp] theorem reduction_points {m n : ℕ} (h : m ≤ n) (a : Residue p n) :
    genericHom (reduction p h) (points p n a) = points p m (reduce p h a) := by
  rw [reduction, genericHom_constantGroupHom]
  exact constantGroupGenericHom_point O K (reduce p h).toAddMonoidHom a

/-- Actual geometric points have the required exponent. -/
theorem killed (n : ℕ) (x : (level p n).Points) : p ^ n • x = 0 := by
  obtain ⟨a, rfl⟩ := (points p n).surjective x
  rw [← map_nsmul, residue_killed, map_zero]

/-- The level exponent supplies the finite-power predicate used by integral exactness. -/
theorem killedByPower (n : ℕ) : KilledByPowerOf p (level p n) := ⟨n, killed p n⟩

/-- Each level has height-one coordinate rank. -/
theorem rank (n : ℕ) : Module.finrank O (level p n).CoordinateRing = p ^ n := by
  rw [FF.coordinate_finrank, constantGroupPoint_card, residue_card]

/-- Inclusions are injective on the actual geometric points. -/
theorem inclusion_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (genericHom (inclusion p h)) := by
  rw [inclusion, genericHom_constantGroupHom]
  exact constantGroupGenericHom_injective O K _ (embed_injective p h)

/-- Reductions are surjective on the actual geometric points. -/
theorem reduction_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (genericHom (reduction p h)) := by
  rw [reduction, genericHom_constantGroupHom]
  exact constantGroupGenericHom_surjective O K _ (reduce_surjective p h)

/-- The original finite point sequence is exact. -/
theorem point_exact (m n : ℕ) :
    Function.Exact (genericHom (inclusion p (Nat.le_add_right m n)))
      (genericHom (reduction p (Nat.le_add_left n m))) := by
  intro x
  obtain ⟨a, rfl⟩ := (points p (m + n)).surjective x
  rw [reduction_points, (points p n).map_eq_zero_iff, residue_exact]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨points p m b, by rw [inclusion_points, hb]⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := (points p m).surjective b
    rw [inclusion_points] at hb
    exact ⟨b, (points p (m + n)).injective hb⟩

end ThreeAdicPlan.ConstantRationalPower
