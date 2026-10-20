/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTraceGluing

/-!
# Comparing the glued trace with a global finite basis

If the whole morphism admits a global finite basis, every local chart trace
is the restriction of the usual multiplication trace. Thus the constructed
trace agrees with it regardless of the independent chart choices.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineTraceGlobalBasis
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
  {ι : Type v} [Finite ι]

/-- A global finite basis identifies every chart trace with ordinary restriction. -/
theorem chart_eq_restrict (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U) :
    let _ := f.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      AffineTraceCharts.chart f U hU s =
        Y.presheaf.map (homOfLE le_top).op (AffineCartesianTrace.sectionTrace f s) := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  unfold AffineTraceCharts.chart
  rw [AffineCartesianTrace.sectionTrace_pullback f
    (isPullback_morphismRestrict f U.1).flip basis]
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable [IsAffineHom f] {κ : Type w} (U : κ → Y.affineOpens)
  (hU : ∀ j, AffineOpenNorm.HasBasis f (U j)) (hcover : ⨆ j, (U j).1 = ⊤)

/-- All independent local traces glue to the actual global multiplication trace. -/
theorem trace_eq_sectionTrace :
    let _ := f.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      AffineTraceGluing.trace f U hU hcover s = AffineCartesianTrace.sectionTrace f s := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  symm
  apply AffineTraceGluing.eq_trace
  intro j
  exact (chart_eq_restrict f (U j) (hU j) basis s).symm

end FLT.Mazur.AffineTraceGlobalBasis
