/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedInertiaKernel

/-!
# Continuous descent through the unramified quotient

Restriction is a continuous surjection from a compact group to a Hausdorff
group, hence a quotient map. Its proved inertia kernel gives unique continuous
factorization of every inertia-trivial homomorphism.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "R" => v.adicCompletionIntegers F
local notation "C" => AlgebraicClosure K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)]

/-- Restriction to the constructed unramified union is a quotient map for the Krull topology. -/
theorem unramifiedRestriction_isQuotientMap :
    Topology.IsQuotientMap (unramifiedRestriction R K C) := by
  let := maximalUnramified_isGalois R K C
  let : T2Space Gal(maximalUnramified R K C/K) := krullTopology_t2
  exact .of_surjective_continuous (unramifiedRestriction_surjective R K C)
    (unramifiedRestriction_continuous R K C)

/-- Every continuous inertia-trivial homomorphism factors uniquely and continuously
through the constructed unramified quotient. -/
theorem existsUnique_unramified_descent {A : Type*} [Group A] [TopologicalSpace A]
    (χ : Gal(C/K) →ₜ* A) (hχ : localInertiaGroup v ≤ χ.toMonoidHom.ker) :
    ∃! ψ : Gal(maximalUnramified R K C/K) →ₜ* A,
      ∀ σ, ψ (unramifiedRestriction R K C σ) = χ σ := by
  let f := unramifiedRestriction R K C
  have hf := unramifiedRestriction_surjective R K C
  have hk : f.ker ≤ χ.toMonoidHom.ker := by
    rw [unramifiedRestriction_ker_eq_localInertia v]
    exact hχ
  let g := f.liftOfSurjective hf ⟨χ.toMonoidHom, hk⟩
  have hg (σ : Gal(C/K)) : g (f σ) = χ σ :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ σ
  have hc : Continuous g := (unramifiedRestriction_isQuotientMap v).continuous_iff.mpr (by
    change Continuous (g ∘ f)
    convert χ.continuous using 1
    exact funext hg)
  refine ⟨⟨g, hc⟩, hg, ?_⟩
  intro ψ hψ
  ext τ
  obtain ⟨σ, rfl⟩ := hf τ
  exact (hψ σ).trans (hg σ).symm

end LocalClassFieldTheory
