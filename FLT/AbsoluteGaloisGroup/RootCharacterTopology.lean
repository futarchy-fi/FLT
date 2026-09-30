/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuity of reduced root characters

A root character is constant on each fiber of the action on its root.
These fibers are open in the Krull topology. Thus the character is locally
constant and continuous, has open kernel, and has finite image.
-/

@[expose] public section

open NumberField

namespace LocalRoot

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "L" => AlgebraicClosure (v.adicCompletion K)
local notation3 "A" => IntegralClosure (v.adicCompletionIntegers K) L

variable {n : ℕ} (hn : 0 < n) {a : v.adicCompletion K} (ha : a ≠ 0)
variable {α : AlgebraicClosure (v.adicCompletion K)}
  (hα : α ^ n = algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) a)

/-- The root character is constant on open fibers of the action on the root. -/
theorem character_isLocallyConstant : IsLocallyConstant (character v hn ha hα) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro σ
  refine ⟨{τ | τ.1 α = σ.1 α}, ?_, rfl, ?_⟩
  · exact (ContinuousSMulDiscrete.isOpen_smul_eq
      (Field.absoluteGaloisGroup (v.adicCompletion K)) α (σ.1 α)).preimage
        continuous_subtype_val
  · intro τ hτ
    apply Units.ext
    change IsLocalRing.residue A (integralRatio v hn ha hα τ) =
      IsLocalRing.residue A (integralRatio v hn ha hα σ)
    congr 1
    apply Subtype.ext
    exact congrArg (fun x : L ↦ x / α) hτ

/-- In particular the character is continuous when its target is discrete. -/
theorem character_continuous [TopologicalSpace (IsLocalRing.ResidueField A)ˣ] :
    Continuous (character v hn ha hα) :=
  (character_isLocallyConstant v hn ha hα).continuous

/-- A reduced root character has open kernel in local inertia. -/
theorem character_ker_isOpen :
    IsOpen ((character v hn ha hα).ker : Set (localInertiaGroup v)) :=
  (character_isLocallyConstant v hn ha hα).isOpen_fiber 1

/-- Its image is finite, since it consists of roots of unity of a fixed positive degree. -/
theorem character_range_finite : Finite (character v hn ha hα).range := by
  let : NeZero n := ⟨hn.ne'⟩
  let f : (character v hn ha hα).range → rootsOfUnity n (IsLocalRing.ResidueField A) :=
    fun x ↦ ⟨x.1, by
      obtain ⟨σ, hσ⟩ := x.2
      rw [mem_rootsOfUnity, ← hσ]
      exact character_pow v hn ha hα σ⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : rootsOfUnity n (IsLocalRing.ResidueField A) ↦ z.1) h

end LocalRoot
