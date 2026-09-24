/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.DedekindDomain.Completion.BaseChange
public import FLT.Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Embedding a global field through a completion

The tensor-product decomposition realizes any embedding over a completed base field
through one of the completions of the global extension.
-/

@[expose] public section

open NumberField IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

/-- A global embedding into a field over the completion factors through a completion above it. -/
theorem NumberField.exists_adicCompletion_embedding
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {Ω : Type*} [Field Ω] [Algebra (v.adicCompletion K) Ω]
    [Algebra K Ω] [IsScalarTower K (v.adicCompletion K) Ω]
    (j : L →ₐ[K] Ω) :
    ∃ (w : v.Extension (𝓞 L)) (g : w.1.adicCompletion L →ₐ[v.adicCompletion K] Ω),
      ∀ x : L, g (algebraMap L _ x) = j x := by
  let := Extension.finite (𝓞 K) K L (𝓞 L) v
  let t : L ⊗[K] v.adicCompletion K →ₐ[K] Ω :=
    Algebra.TensorProduct.lift j (IsScalarTower.toAlgHom K _ Ω) (fun _ _ ↦ .all _ _)
  let e := adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
  obtain ⟨w, g, hg⟩ := (t.toRingHom.comp e.symm.toRingHom).exists_eq_comp_eval
  have ht (z : L ⊗[K] v.adicCompletion K) : g (e z w) = t z := by
    have h := RingHom.congr_fun hg (e z)
    simpa using h
  have hleft (x : L) : g (algebraMap L _ x) = j x := by
    simpa [e, adicCompletion.baseChangeAlgEquiv,
      adicCompletion.baseChange_tmul_apply, t] using ht (x ⊗ₜ 1)
  have hright (x : v.adicCompletion K) : g (algebraMap _ _ x) = algebraMap _ Ω x := by
    simpa [e, adicCompletion.baseChangeAlgEquiv,
      adicCompletion.baseChange_tmul_apply, t] using ht (1 ⊗ₜ x)
  exact ⟨w, ⟨g, hright⟩, hleft⟩

