/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicIntegerSpace
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Evaluation of integral series in the complete DVR

The coefficient ring is discrete, and the target copy carries the proved
complete adic topology. Evaluation respects substitution and preserves
topological nilpotence for series with zero constant coefficient.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries IsLocalRing
open scoped Topology

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The natural inclusion from the topological integer copy into its field. -/
def adicIntegerToField : AdicInteger S L →+* L :=
  (algebraMap S L).comp (adicIntegerEquiv S L).toRingHom

/-- The integer inclusion induces exactly its constructed uniformity. -/
theorem adicIntegerToField_isUniformInducing :
    letI := dvrAdicValued S L
    IsUniformInducing (adicIntegerToField S L) := by
  let := dvrAdicValued S L
  exact ⟨rfl⟩

/-- An integer of value less than one is topologically nilpotent. -/
theorem adicInteger_hasEval (x : AdicInteger S L)
    (hx : (dvrPrime S).valuation L (adicIntegerToField S L x) < 1) : HasEval x := by
  let := dvrAdicValued S L
  apply (adicIntegerToField_isUniformInducing S L).isInducing.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, map_pow, map_zero] using
    (Valued.tendsto_zero_pow_of_v_lt_one hx)

/-- Evaluate a series with discrete DVR coefficients in the adic integer copy. -/
def adicSeriesEval (f : PowerSeries S) (x : AdicInteger S L) : AdicInteger S L :=
  letI : UniformSpace S := ⊥
  PowerSeries.eval₂ (algebraMap S (AdicInteger S L)) x f

variable [IsAdicComplete (maximalIdeal S) S]

/-- Evaluation is the sum of the actual monomials in the complete integer ring. -/
theorem adicSeriesEval_hasSum (f : PowerSeries S) (x : AdicInteger S L) (hx : HasEval x) :
    HasSum (fun n => algebraMap S (AdicInteger S L) (coeff n f) * x ^ n)
      (adicSeriesEval S L f x) := by
  let : UniformSpace S := ⊥
  exact PowerSeries.hasSum_eval₂ (continuous_of_discreteTopology) hx f

omit [IsAdicComplete (maximalIdeal S) S] in
/-- Evaluating X returns its argument. -/
theorem adicSeriesEval_X (x : AdicInteger S L) : adicSeriesEval S L X x = x := by
  let : UniformSpace S := ⊥
  exact PowerSeries.eval₂_X _ _

/-- Evaluation commutes with composition of integral power series. -/
theorem adicSeriesEval_subst (f g : PowerSeries S) (hg : constantCoeff g = 0)
    (x : AdicInteger S L) (hx : HasEval x) :
    adicSeriesEval S L (f.subst g) x =
      adicSeriesEval S L f (adicSeriesEval S L g x) := by
  let : UniformSpace S := ⊥
  exact MvPowerSeries.eval₂_subst (HasSubst.of_constantCoeff_zero hg).const
    (PowerSeries.hasEval hx) f

/-- A zero-constant series evaluated at a nilpotent point remains topologically nilpotent. -/
theorem adicSeriesEval_hasEval (f : PowerSeries S) (hf : constantCoeff f = 0)
    (x : AdicInteger S L) (hx : HasEval x) : HasEval (adicSeriesEval S L f x) := by
  let : UniformSpace S := ⊥
  obtain ⟨g, rfl⟩ := X_dvd_iff.mpr hf
  change HasEval (PowerSeries.eval₂ (algebraMap S (AdicInteger S L)) x (X * g))
  rw [← PowerSeries.coe_eval₂Hom (continuous_of_discreteTopology) hx, map_mul]
  have hX : PowerSeries.eval₂Hom (φ := algebraMap S (AdicInteger S L))
      (continuous_of_discreteTopology) hx X = x := by
    rw [PowerSeries.coe_eval₂Hom]
    exact PowerSeries.eval₂_X _ _
  rw [hX, mul_comm]
  exact hx.mul_left _

end LocalClassFieldTheory
