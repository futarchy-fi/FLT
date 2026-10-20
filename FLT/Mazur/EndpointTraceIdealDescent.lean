/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Descending the full endpoint trace ideal

When second-endpoint functions span the relation algebra, their traces generate
exactly the image ideal of the whole multiplication trace. Integral injective
scalar inclusion then descends unit generation to the original invariant ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.EndpointTraceIdealDescent
variable {A B C Ω : Type*} [CommRing A] [AddCommGroup B] [Module A B]
  [CommRing Ω] (q : C → B) (τ : B →ₗ[A] A)

/-- Endpoint spanning identifies the generated trace ideal with the full trace image. -/
theorem span_trace_eq_range (hq : Submodule.span A (Set.range q) = ⊤) :
    Ideal.span (Set.range (fun c ↦ τ (q c))) = LinearMap.range τ := by
  change Submodule.span A (Set.range (fun c ↦ τ (q c))) = _
  rw [Set.range_comp', ← Submodule.map_span, hq,
    Submodule.map_top]

/-- A surjective full trace gives a unit ideal of endpoint traces. -/
theorem span_trace_eq_top (hq : Submodule.span A (Set.range q) = ⊤)
    (hτ : Function.Surjective τ) :
    Ideal.span (Set.range (fun c ↦ τ (q c))) = ⊤ := by
  rw [span_trace_eq_range q τ hq, LinearMap.range_eq_top.mpr hτ]

/-- Invariant trace coordinates commute with extension of the generated ideal. -/
theorem map_traceIdeal (σ : Ω →+* A) (T : C → Ω)
    (hT : ∀ c, σ (T c) = τ (q c)) :
    (Ideal.span (Set.range T)).map σ = Ideal.span (Set.range (fun c ↦ τ (q c))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext hT)

/-- Integral faithful scalar inclusion descends endpoint-trace unit generation. -/
theorem traceIdeal_eq_top (σ : Ω →+* A) (hσ : Function.Injective σ)
    (hι : σ.IsIntegral) (T : C → Ω) (hT : ∀ c, σ (T c) = τ (q c))
    (hq : Submodule.span A (Set.range q) = ⊤) (hτ : Function.Surjective τ) :
    Ideal.span (Set.range T) = ⊤ := by
  apply (Ideal.map_eq_top_iff σ hσ hι).mp
  rw [map_traceIdeal q τ σ T hT]
  exact span_trace_eq_top q τ hq hτ

end FLT.Mazur.EndpointTraceIdealDescent
