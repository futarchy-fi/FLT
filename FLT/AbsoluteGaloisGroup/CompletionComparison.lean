/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaComparison
public import FLT.DedekindDomain.Completion.Embedding

/-!
# The completion at the prime induced by a local embedding

The chosen embedding of algebraic closures factors through the completion at
`localInducedPrime`. Its map on integers reflects the maximal ideal.
-/

@[expose] public section

open NumberField IsDedekindDomain.HeightOneSpectrum

namespace NumberField.InertiaComparison
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
variable (w : v.Extension (𝓞 L))
local notation "Kv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K
local notation "Lw" => adicCompletion L w.val
local notation "Ow" => adicCompletionIntegers L w.val
local notation "A" => IntegralClosure Ov (AlgebraicClosure Kv)

/-- Extend a completion embedding to its integer ring. -/
noncomputable def completionIntegersMap (g : Lw →ₐ[Kv] AlgebraicClosure Kv) : Ow →+* A := by
  letI : IsScalarTower Ov Ow Lw := .of_algebraMap_smul fun _ _ ↦ rfl
  exact {
    toFun x := ⟨g x.1, by
      have : IsIntegral Ov (x : Lw) :=
        (Algebra.IsIntegral.isIntegral (R := Ov) x).map (IsScalarTower.toAlgHom Ov Ow Lw)
      exact this.map (g.restrictScalars Ov)⟩
    map_zero' := Subtype.ext (map_zero g)
    map_one' := Subtype.ext (map_one g)
    map_add' x y := Subtype.ext (map_add g x.1 y.1)
    map_mul' x y := Subtype.ext (map_mul g x.1 y.1) }

/-- The map of integer rings induced by a completion embedding reflects units. -/
theorem completionIntegersMap_isLocalHom (g : Lw →ₐ[Kv] AlgebraicClosure Kv) :
    IsLocalHom (completionIntegersMap v w g) := by
  let f := completionIntegersMap v w g
  have hcomp : f.comp (algebraMap Ov Ow) = algebraMap Ov A := by
    ext x
    apply Subtype.ext
    exact (g.restrictScalars Ov).commutes x
  have hint : f.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap Ov Ow)
    rw [hcomp]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  apply hint.isLocalHom
  intro x y h
  exact Subtype.ext (g.injective (congrArg Subtype.val h))

/-- The maximal ideal pulls back to the maximal ideal of the completed integer ring. -/
theorem completionIntegersMap_mem_maximalIdeal
    (g : Lw →ₐ[Kv] AlgebraicClosure Kv) (x : Ow) :
    completionIntegersMap v w g x ∈ IsLocalRing.maximalIdeal A ↔
      x ∈ w.1.completionIdeal L := by
  let := completionIntegersMap_isLocalHom v w g
  simp only [completionIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (isUnit_map_iff (completionIntegersMap v w g) x)

end NumberField.InertiaComparison

namespace NumberField.InertiaComparison
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
local notation "Kv" => v.adicCompletion K

/-- The chosen local embedding identifies the prime selected by tensor decomposition. -/
theorem inducedPrime_eq_of_completion_embedding
    (w : v.Extension (𝓞 L))
    (g : w.1.adicCompletion L →ₐ[Kv] AlgebraicClosure Kv)
    (hg : ∀ x : L, g (algebraMap L _ x) =
      AlgebraicClosure.map (algebraMap K Kv) (L.val x)) :
    localInducedPrime v L = w.1.asIdeal := by
  ext x
  change localIntegersMap v L x ∈ IsLocalRing.maximalIdeal _ ↔ _
  have hx : localIntegersMap v L x =
      completionIntegersMap v w g (algebraMap (𝓞 L) (w.1.adicCompletionIntegers L) x) := by
    apply Subtype.ext
    exact (hg x.1).symm
  rw [hx, completionIntegersMap_mem_maximalIdeal,
    ← Ideal.mem_of_liesOver (w.1.completionIdeal L) w.1.asIdeal]

/-- The chosen closure embedding extends to the completion at its induced global prime. -/
theorem exists_inducedPrime_completion_embedding :
    ∃ (w : v.Extension (𝓞 L)) (g : w.1.adicCompletion L →ₐ[Kv] AlgebraicClosure Kv),
      localInducedPrime v L = w.1.asIdeal ∧
      ∀ x : L, g (algebraMap L _ x) =
        AlgebraicClosure.map (algebraMap K Kv) (L.val x) := by
  let j : L →ₐ[K] AlgebraicClosure Kv := {
    __ := (AlgebraicClosure.map (algebraMap K Kv)).comp L.val.toRingHom
    commutes' := fun x ↦ AlgebraicClosure.map_algebraMap _ x }
  obtain ⟨w, g, hg⟩ := NumberField.exists_adicCompletion_embedding v j
  exact ⟨w, g, inducedPrime_eq_of_completion_embedding v L w g hg, hg⟩

end NumberField.InertiaComparison

namespace NumberField.InertiaComparison
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
variable (w : v.Extension (𝓞 L))
local notation "Kv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K
local notation "Lw" => adicCompletion L w.val
local notation "Ow" => adicCompletionIntegers L w.val
variable {E : Type*} [Field E] [Algebra (v.adicCompletion K) E]
variable [Algebra (v.adicCompletionIntegers K) E]
variable [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]

/-- A local field isomorphism identifies completed integers with the integral closure. -/
noncomputable def completionIntegersEquivIntegralClosure (e : Lw ≃ₐ[Kv] E) :
    Ow ≃ₐ[Ov] IntegralClosure Ov E := by
  letI : IsScalarTower Ov Ow Lw := .of_algebraMap_smul fun _ _ ↦ rfl
  let f : Ow →ₐ[Ov] IntegralClosure Ov E := {
    toFun := fun x ↦ ⟨e x.1, by
      have hx : IsIntegral Ov (x : Lw) :=
        (Algebra.IsIntegral.isIntegral (R := Ov) x).map (IsScalarTower.toAlgHom Ov Ow Lw)
      exact hx.map (e.toAlgHom.restrictScalars Ov)⟩
    map_zero' := Subtype.ext (map_zero e)
    map_one' := Subtype.ext (map_one e)
    map_add' := fun x y ↦ Subtype.ext (map_add e x.1 y.1)
    map_mul' := fun x y ↦ Subtype.ext (map_mul e x.1 y.1)
    commutes' := fun x ↦ Subtype.ext ((e.restrictScalars Ov).commutes x) }
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro y
    have hy : IsIntegral Ov (e.symm y.1) := y.2.map (e.symm.toAlgHom.restrictScalars Ov)
    obtain ⟨x, hx⟩ := (IsIntegralClosure.isIntegral_iff (A := Ow)).mp hy
    refine ⟨x, Subtype.ext ?_⟩
    change e (algebraMap Ow Lw x) = y.1
    rw [hx, e.apply_symm_apply]

end NumberField.InertiaComparison

namespace NumberField.InertiaComparison
variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
variable (w : v.Extension (𝓞 L))
local notation "Kv" => v.adicCompletion K
local notation "Ov" => v.adicCompletionIntegers K

/-- Ramification indices agree for a global prime and any realization of its completion. -/
lemma ramificationIdx_eq_of_completion_equiv
    (C : IntermediateField Kv (AlgebraicClosure Kv)) [FiniteDimensional Kv C]
    (e : w.1.adicCompletion L ≃ₐ[Kv] C) :
    w.1.asIdeal.ramificationIdx (𝓞 K) =
      (IsLocalRing.maximalIdeal (IntegralClosure Ov C)).ramificationIdx Ov := by
  let B := IntegralClosure Ov C
  let p := IsLocalRing.maximalIdeal Ov
  let P := IsLocalRing.maximalIdeal B
  let f := completionIntegersEquivIntegralClosure v w e
  let : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain Ov Kv C (integralClosure Ov C)
  let : Module.IsTorsionFree Ov B := by
    rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap Kv C).injective
    exact congrArg Subtype.val hxy
  let : Module.IsTorsionFree Ov (w.1.adicCompletionIntegers L) :=
    Function.Injective.moduleIsTorsionFree f f.injective (fun r x ↦ f.toLinearEquiv.map_smul r x)
  let : P.LiesOver p := by dsimp only [P, p]; infer_instance
  let : (w.1.completionIdeal L).LiesOver p :=
    adicCompletion.liesOver_completionIdeal K L w
  have hm : P.comap f = w.1.completionIdeal L :=
    IsLocalRing.maximalIdeal_comap f.toRingHom
  have he := Ideal.ramificationIdx'_comap_eq p f P
  rw [hm, Ideal.ramificationIdx'_eq_ramificationIdx p _ (v.completionIdeal_ne_bot K),
    Ideal.ramificationIdx'_eq_ramificationIdx p _ (v.completionIdeal_ne_bot K)] at he
  exact (adicCompletion.ramificationIdx_eq_ramificationIdx K L w).symm.trans he

end NumberField.InertiaComparison
