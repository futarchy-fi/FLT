/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianTrace
public import FLT.Mazur.AffineOpenNorm
public import FLT.Mazur.AffineNormCartesianCharts

/-!
# Traces on independent finite free affine charts

Restriction and cartesian transport preserve the trace of the whole source
preimage even when target charts use different finite bases and ranks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineTraceCharts
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The trace on an actual affine target chart with a finite free whole preimage. -/
def chart (U : Y.affineOpens) (_hU : AffineOpenNorm.HasBasis f U)
    (s : Γ(X, ⊤)) : Γ(Y, U.1) :=
  U.1.topIso.hom (AffineCartesianTrace.sectionTrace (f ∣_ U.1)
    ((f ⁻¹ᵁ U.1).ι.appTop s))

/-- The chart trace in the section ring of the open subscheme. -/
theorem chart_top (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    (s : Γ(X, ⊤)) :
    U.1.topIso.inv (chart f U hU s) =
      AffineCartesianTrace.sectionTrace (f ∣_ U.1)
        ((f ⁻¹ᵁ U.1).ι.appTop s) := by
  exact Iso.hom_inv_id_apply _ _

variable [IsAffineHom f]

/-- Traces commute with restriction to a separately based smaller chart. -/
theorem chart_restrict {U V : Y.affineOpens} (hU : AffineOpenNorm.HasBasis f U)
    (hV : AffineOpenNorm.HasBasis f V) (h : V ≤ U) (s : Γ(X, ⊤)) :
    Y.presheaf.map (homOfLE h).op (chart f U hU s) = chart f V hV s := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  unfold chart
  erw [Approximation.topIso_hom_restriction (X := Y) h]
  congr 1
  have hc := AffineCartesianTrace.sectionTrace_pullback (f ∣_ U.1)
      (AffinePreimageRestriction.isPullback f h) hU.choose_spec.some ((f ⁻¹ᵁ U.1).ι.appTop s)
  rw [← hc]
  congr 1
  exact congrArg (fun k : (f ⁻¹ᵁ V.1).toScheme ⟶ X ↦ k.appTop s)
    (Scheme.homOfLE_ι X (f.preimage_mono h))

variable {P T : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ Y}
  (H : IsPullback a b f g)

include H in
/-- Cartesian transport compares the trace on unrelated actual target charts. -/
theorem chart_pullback (U : Y.affineOpens) (V : T.affineOpens)
    (h : V.1 ≤ g ⁻¹ᵁ U.1) (hU : AffineOpenNorm.HasBasis f U)
    (hV : AffineOpenNorm.HasBasis b V) (s : Γ(X, ⊤)) :
    chart b V hV (a.appTop s) = g.appLE U.1 V.1 h (chart f U hU s) := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  apply (ConcreteCategory.bijective_of_isIso V.1.topIso.inv).injective
  rw [chart_top]
  have ht : V.1.topIso.inv (g.appLE U.1 V.1 h (chart f U hU s)) =
      (g.resLE U.1 V.1 h).appTop (U.1.topIso.inv (chart f U hU s)) := by
    have he := Approximation.topIso_hom_resLE g U.1 V.1 h
      (U.1.topIso.inv (chart f U hU s))
    simpa only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] using
      congrArg V.1.topIso.inv he
  rw [ht, chart_top]
  have hc := AffineCartesianTrace.sectionTrace_pullback (f ∣_ U.1)
      (AffineNormCartesianCharts.isPullback H U V h) hU.choose_spec.some
      ((f ⁻¹ᵁ U.1).ι.appTop s)
  rw [← hc]
  congr 1
  exact congrArg (fun k : (b ⁻¹ᵁ V.1).toScheme ⟶ X ↦ k.appTop s)
    (Scheme.Hom.resLE_comp_ι a (AffineNormCartesianCharts.source_le H U V h)).symm

end FLT.Mazur.AffineTraceCharts
