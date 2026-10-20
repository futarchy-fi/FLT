/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTraceLinearity

/-!
# The linear map of glued traces

The trace constructed from independent finite free charts is a linear map
over the original target ring. Its chart comparison uses actual open subschemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineTraceGluing
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The full glued trace as a linear map, without a global basis. -/
def linearMap :
    let _ := f.appTop.hom.toAlgebra
    Γ(X, ⊤) →ₗ[Γ(Y, ⊤)] Γ(Y, ⊤) := by
  let _ := f.appTop.hom.toAlgebra
  exact { toFun := trace f U hU hcover
          map_add' := trace_add f U hU hcover
          map_smul' := trace_mul f U hU hcover }

/-- Restriction to any finite free open computes the full local trace. -/
theorem trace_openRestrict (V : Y.affineOpens) (hV : AffineOpenNorm.HasBasis f V)
    (s : Γ(X, ⊤)) :
    V.1.ι.appTop (trace f U hU hcover s) =
      AffineCartesianTrace.sectionTrace (f ∣_ V.1) ((f ⁻¹ᵁ V.1).ι.appTop s) := by
  rw [← AffineTraceCharts.chart_top f V hV s,
    ← trace_any_chart f U hU hcover V hV s]
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end FLT.Mazur.AffineTraceGluing
