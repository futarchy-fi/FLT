/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
/-!
# Local-field structures on finite extensions

The spectral norm extends the norm of a nonarchimedean local field to every
finite field extension. The resulting topology is locally compact, the inclusion
is valuative and continuous, and base-field automorphisms preserve the valuation.
-/

@[expose] public section

open ValuativeRel
open scoped Topology NNReal
namespace TateCurve
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]
/-- Every finite extension admits a compatible local-field structure with continuous,
valuation-preserving base-field automorphisms. -/
theorem exists_localField_extension : ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
    IsNonarchimedeanLocalField L ∧ ValuativeExtension K L ∧
      Continuous (algebraMap K L) ∧
      ∀ σ : L ≃ₐ[K] L, Continuous σ ∧ ∀ x : L, valuation L (σ x) = valuation L x := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  let : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  have : IsUltrametricDist L := ⟨fun x y z ↦ by
    change spectralNorm K L (x - z) ≤ _
    rw [show x - z = (x - y) + (y - z) by ring]
    exact isNonarchimedean_spectralNorm _ _⟩
  let : ValuativeRel L := .ofValuation (NormedField.valuation (K := L))
  let : (NormedField.valuation (K := L)).Compatible := .ofValuation _
  have : IsValuativeTopology L := by
    let : Valued L ℝ≥0 := NormedField.toValued
    exact IsValuativeTopology.of_mem_nhds_iff_vle NormedField.valuation Valued.mem_nhds
  have : ProperSpace L := FiniteDimensional.proper K L
  have : ValuativeRel.IsNontrivial L :=
    (isNontrivial_iff_isNontrivial NormedField.valuation).mpr inferInstance
  have : IsNonarchimedeanLocalField L := {}
  have he : ValuativeExtension K L := by
    constructor
    intro a b
    change ‖algebraMap K L a‖₊ ≤ ‖algebraMap K L b‖₊ ↔ a ≤ᵥ b
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
      norm_algebraMap', norm_algebraMap', Valued.toNormedField.norm_le_iff]
    exact (Valuation.Compatible.vle_iff_le (v := Valued.v) (x := a) (y := b)).symm
  refine ⟨inferInstance, inferInstance, inferInstance, he, continuous_algebraMap K L, ?_⟩
  intro σ
  refine ⟨σ.toLinearMap.continuous_of_finiteDimensional, fun x ↦ ?_⟩
  apply (valuation L).veq_iff_eq.mp
  apply (NormedField.valuation (K := L)).veq_iff_eq.mpr
  apply NNReal.coe_injective
  exact (spectralNorm_eq_of_equiv σ x).symm
end TateCurve
