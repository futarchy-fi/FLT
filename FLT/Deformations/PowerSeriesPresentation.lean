/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ProartinianAdicTopology
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Finite-variable power-series presentations of local proartinian algebras

Use generators of the entire maximal ideal, including coefficient directions.
Then power series over the original coefficient ring suffice: completeness of
that coefficient ring is not needed. The source is complete for its variable
ideal; the target has its actual maximal-ideal-adic topology.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open IsLocalRing Filter MvPowerSeries
namespace Deformation.ProartinianCat

variable {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  (A : ProartinianCat O)

/-- Finite generation of the maximal ideal gives a surjection from a power-series
algebra over the original coefficient ring. -/
theorem exists_powerSeries_surjection_of_maximalIdeal_fg (hfg : (maximalIdeal A).FG) :
    ∃ n : ℕ, ∃ f : MvPowerSeries (Fin n) O →ₐ[O] A, Function.Surjective f := by
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hxm (i : Fin n) : x i ∈ maximalIdeal A := by
    rw [← hx]
    exact Submodule.subset_span ⟨i, rfl⟩
  let : IsAdicTopology A := isAdicTopology_of_maximalIdeal_fg A hfg
  let : IsHausdorff (maximalIdeal A) A := isHausdorff_maximalIdeal_of_fg A hfg
  let : TopologicalSpace O := ⊥
  let : DiscreteTopology O := ⟨rfl⟩
  let : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  let : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace A := IsProartinian.toCompleteSpace
  have heval : HasEval x := by
    constructor
    · intro i
      apply (hasBasis_maximalIdeal_pow A).tendsto_right_iff.mpr
      intro r _
      filter_upwards [eventually_ge_atTop r] with s hs
      exact (Ideal.pow_le_pow_right hs) (Ideal.pow_mem_pow (hxm i) s)
    · simp only [Filter.cofinite_eq_bot, tendsto_bot]
  let f : MvPowerSeries (Fin n) O →ₐ[O] A :=
    { MvPowerSeries.eval₂Hom (φ := algebraMap O A) continuous_of_discreteTopology heval with
      commutes' := fun o ↦ by
        change MvPowerSeries.eval₂Hom _ _ (C o) = _
        rw [coe_eval₂Hom, eval₂_C] }
  let I : Ideal (MvPowerSeries (Fin n) O) := Ideal.span (Set.range X)
  have hmap : I.map f.toRingHom = maximalIdeal A := by
    rw [Ideal.map_span, ← Set.range_comp]
    have hfX : (f.toRingHom : MvPowerSeries (Fin n) O → A) ∘ X = x := by
      funext i
      change MvPowerSeries.eval₂Hom (φ := algebraMap O A)
        continuous_of_discreteTopology heval (X i) = x i
      rw [coe_eval₂Hom, eval₂_X]
    rw [hfX]
    exact hx
  have hsur : Function.Surjective ((Ideal.Quotient.mk (I.map f.toRingHom)).comp f.toRingHom) := by
    rw [hmap]
    intro y
    obtain ⟨o, ho⟩ := IsResidueAlgebra.algebraMap_surjective O A y
    refine ⟨C o, ?_⟩
    change residue A (f (algebraMap O (MvPowerSeries (Fin n) O) o)) = y
    rw [f.commutes]
    exact ho
  let : IsHausdorff (I.map f.toRingHom) A := hmap ▸ inferInstance
  exact ⟨n, f, surjective_of_mk_map_comp_surjective (I := I) f.toRingHom hsur⟩

/-- The presentation proves Noetherianity, rather than assuming it from tangent finiteness. -/
theorem isNoetherianRing_of_maximalIdeal_fg [IsNoetherianRing O]
    (hfg : (maximalIdeal A).FG) : IsNoetherianRing A := by
  obtain ⟨n, f, hf⟩ := exists_powerSeries_surjection_of_maximalIdeal_fg A hfg
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) O) A f.toRingHom hf

end Deformation.ProartinianCat
