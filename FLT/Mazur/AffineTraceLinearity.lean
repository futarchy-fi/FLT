/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTraceGluing

/-!
# Linearity of glued full-source traces

Target sections can be taken outside each chart trace, hence outside the trace
in the original global section ring. No constant-rank choice is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffineTraceCharts
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The trace on a finite free chart is additive. -/
theorem chart_add (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    (s t : Γ(X, ⊤)) : chart f U hU (s + t) = chart f U hU s + chart f U hU t := by
  simp only [chart, map_add, AffineCartesianTrace.sectionTrace_add]

/-- Actual target sections can be taken outside a chart trace. -/
theorem chart_mul (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) :
    chart f U hU (f.appTop r * s) =
      Y.presheaf.map (homOfLE le_top).op r * chart f U hU s := by
  have he : (f ⁻¹ᵁ U.1).ι.appTop (f.appTop r) =
      (f ∣_ U.1).appTop (U.1.ι.appTop r) := by
    exact congrArg (fun k : (f ⁻¹ᵁ U.1).toScheme ⟶ Y ↦ k.appTop r)
      (morphismRestrict_ι f U.1).symm
  unfold chart
  rw [map_mul, he, AffineCartesianTrace.sectionTrace_mul, map_mul]
  congr 1
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end FLT.Mazur.AffineTraceCharts
namespace FLT.Mazur.AffineTraceGluing
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The global trace is additive. -/
theorem trace_add (s t : Γ(X, ⊤)) :
    trace f U hU hcover (s + t) = trace f U hU hcover s + trace f U hU hcover t := by
  symm
  apply eq_trace
  intro i
  rw [map_add, trace_chart, trace_chart, AffineTraceCharts.chart_add]

/-- The global trace is linear over the unchanged target section ring. -/
theorem trace_mul (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) :
    trace f U hU hcover (f.appTop r * s) = r * trace f U hU hcover s := by
  symm
  apply eq_trace
  intro i
  rw [map_mul, trace_chart, AffineTraceCharts.chart_mul]

end FLT.Mazur.AffineTraceGluing
