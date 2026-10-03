/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnitNormSequence
public import FLT.LocalClassFieldTheory.PrincipalAdicLimit
public import FLT.LocalClassFieldTheory.NormCongruence
public import FLT.GroupScheme.FiniteFreeAdicComplete

/-!
# Surjectivity of the unramified unit norm

The constructed successive corrections converge by adic completeness. Norm
congruence and separatedness make their limiting norm exactly the target unit.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [Finite (ResidueField R)]
  [IsAdicComplete (maximalIdeal R) R]

/-- Every base unit is the norm of an integral unit in the complete unramified DVR. -/
theorem unramified_unit_norm_surjective : Function.Surjective (Units.map (Algebra.norm R) :
    Sˣ →* Rˣ) := by
  let : IsAdicComplete (maximalIdeal S) S := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)]
    exact ThreeAdicPlan.adicComplete_finite_free_algebra (maximalIdeal R) S
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : IsPrecomplete (Ideal.span {algebraMap R S π}) S := by
    rw [← unramified_maximalIdeal_eq R S hπ]
    infer_instance
  let : IsHausdorff (Ideal.span {π}) R := by
    rw [← hπ.maximalIdeal_eq]
    infer_instance
  intro u
  let f : ℕ → S := fun n => ((unitNormApproximation R S hπ u n).val : S)
  obtain ⟨x, hx⟩ := exists_principal_adic_limit (algebraMap R S π) f (fun n =>
    (pow_dvd_pow _ (Nat.le_succ n)).trans (unitNormApproximation_step R S hπ u n))
  have he : residue S (f 1) = residue S x := by
    apply sub_eq_zero.mp
    rw [← map_sub, residue_eq_zero_iff, unramified_maximalIdeal_eq R S hπ,
      Ideal.mem_span_singleton]
    simpa only [pow_one] using hx 1
  have hu : IsUnit x := (residue_ne_zero_iff_isUnit x).1 (by
    rw [← he]
    exact (residue_ne_zero_iff_isUnit (f 1)).2 (unitNormApproximation R S hπ u 1).val.isUnit)
  have hn : Algebra.norm R x = (u : R) := by
    apply eq_of_principal_congruent π
    intro n
    have ha := (pow_dvd_pow π (Nat.le_succ n)).trans (unitNormApproximation_norm R S hπ u n)
    have hb := norm_sub_pow_dvd R S π n (f n) x (hx n)
    change π ^ n ∣ Algebra.norm R (f n) - (u : R) at ha
    convert dvd_sub ha hb using 1
    ring
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  change Algebra.norm R (hu.unit : S) = (u : R)
  rw [hu.unit_spec, hn]

end LocalClassFieldTheory
