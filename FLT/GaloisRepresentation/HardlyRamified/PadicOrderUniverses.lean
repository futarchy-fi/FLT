/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PadicOrderCanonicalTopology
public import FLT.GaloisRepresentation.HardlyRamified.OpenPowerUniverses
public import FLT.GaloisRepresentation.HardlyRamified.BaseChangeUniverses
public import FLT.Deformations.RepresentationTheory.PadicIdealOpen

/-!
# Normalization of the original arbitrary-universe representation

Open ideals contain p-powers and have finite quotients, so the constructed
normalization preserves HR. Tensor cancellation retains the original generic member.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace PadicOrderPlan
open GaloisRepresentation TensorProduct

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra ℤ_[p] R]
  [IsDomain R] [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]

/-- Open normalized ideals contain a p-power and have finite quotient. -/
theorem normalizedOrder_open_ideal_universes (J : Ideal (NormalizedOrder p R))
    (hJ : IsOpen (J : Set (NormalizedOrder p R))) :
    ∃ n : ℕ, (p : NormalizedOrder p R) ^ n ∈ J ∧ Finite (NormalizedOrder p R ⧸ J) := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
  have hc : Filter.Tendsto (fun n : ℕ ↦ (p : NormalizedOrder p R) ^ n)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, map_pow, map_natCast, map_zero] using
      (continuous_algebraMap ℤ_[p] (NormalizedOrder p R)).tendsto 0 |>.comp ht
  have he : ∀ᶠ n : ℕ in Filter.atTop, (p : NormalizedOrder p R) ^ n ∈ J :=
    hc (hJ.mem_nhds J.zero_mem)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, hn, IsLocalRing.isOpen_iff_finite_quotient.mp hJ⟩

variable [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsModuleTopology ℤ_[p] R]
  {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]

set_option maxHeartbeats 800000 in
-- Comparing the original and normalized scalar-tower instances needs extra elaboration.
/-- The constructed general-prime normalization preserves all four HR clauses. -/
theorem hardlyRamified_normalization_universes (hpodd : Odd p) (hV : Module.rank R V = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hpodd hV ρ) :
    IsHardlyRamified hpodd
      (show Module.rank (NormalizedOrder p R) (NormalizedOrder p R ⊗[R] V) = 2 by
        simpa [Module.rank_baseChange] using hV)
      (ρ.baseChange (NormalizedOrder p R)) := by
  exact ThreeAdicPlan.hardlyRamified_baseChange_of_flat_universes hpodd hV _ hρ
    (ThreeAdicPlan.flatAt_of_open_powers_universes p
      (PadicInt.isOpen_span_p_pow p R) (normalizedOrder_open_ideal_universes p) ρ _ hρ.isFlat)


omit [IsTopologicalRing R] in
/-- Normalization followed by the original fraction field recovers the original generic member. -/
theorem normalized_generic_equiv_universes (ρ : GaloisRep ℚ R V) :
    letI := fractionNormedField p R
    letI : TopologicalSpace (FractionRing R) :=
      (fractionNormedField p R).toUniformSpace.toTopologicalSpace
    letI : ContinuousSMul R (FractionRing R) := fractionOrderContinuousSMul p R
    letI : ContinuousSMul (NormalizedOrder p R) (FractionRing R) :=
      continuousSMul_of_algebraMap _ _ continuous_subtype_val
    ((ρ.baseChange (NormalizedOrder p R)).baseChange (FractionRing R)).conj
      (AlgebraTensorModule.cancelBaseChange R (NormalizedOrder p R) (FractionRing R)
        (FractionRing R) V) = ρ.baseChange (FractionRing R) := by
  let := fractionNormedField p R
  let : TopologicalSpace (FractionRing R) :=
    (fractionNormedField p R).toUniformSpace.toTopologicalSpace
  let : ContinuousSMul R (FractionRing R) := fractionOrderContinuousSMul p R
  let : ContinuousSMul (NormalizedOrder p R) (FractionRing R) :=
    continuousSMul_of_algebraMap _ _ continuous_subtype_val
  let := moduleTopology (FractionRing R)
    (Module.End (FractionRing R) (FractionRing R ⊗[R] V))
  apply ContinuousMonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  let e := AlgebraTensorModule.cancelBaseChange R (NormalizedOrder p R) (FractionRing R)
    (FractionRing R) V
  change e (((ρ.baseChange (NormalizedOrder p R)).baseChange (FractionRing R)) g
    (e.symm x)) = (ρ.baseChange (FractionRing R)) g x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [e, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      GaloisRep.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp_all

end PadicOrderPlan
