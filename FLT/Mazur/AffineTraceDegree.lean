/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeBoundaryTrace

/-!
# The original relation degree from independent local ranks

The trace of the unit is the basis cardinality on every finite free target
chart. This gives an invariant degree section even when the ranks vary.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineTraceCharts
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The local trace of the unit is the actual basis cardinality. -/
theorem chart_one (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    {ι : Type v} [Fintype ι] :
    let _ := (f ∣_ U.1).appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(U.1.toScheme, ⊤) Γ((f ⁻¹ᵁ U.1).toScheme, ⊤)),
      chart f U hU 1 = (Fintype.card ι : Γ(Y, U.1)) := by
  let _ := (f ∣_ U.1).appTop.hom.toAlgebra
  dsimp only
  intro basis
  have h := AffineCartesianTrace.sectionTrace_scalar (f ∣_ U.1) basis 1
  rw [map_one] at h
  simp only [chart, map_one, h, nsmul_eq_mul, mul_one, map_natCast]

end FLT.Mazur.AffineTraceCharts
namespace FLT.Mazur.AffineLocallyFreeRelationTrace
universe u v
open AffineTraceGluing
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The invariant degree section restricts to the actual local rank, with no common rank. -/
theorem invariantTrace_one_chart (V : A.affineOpens) (hV : AffineOpenNorm.HasBasis p V)
    {κ : Type*} [Fintype κ] :
    let _ := (p ∣_ V.1).appTop.hom.toAlgebra
    ∀ (_basis : Basis κ Γ(V.1.toScheme, ⊤) Γ((p ⁻¹ᵁ V.1).toScheme, ⊤)),
      A.presheaf.map (homOfLE le_top).op (invariantTrace p q U hU hcover e 1).val =
        (Fintype.card κ : Γ(A, V.1)) := by
  let _ := (p ∣_ V.1).appTop.hom.toAlgebra
  dsimp only
  intro basis
  change A.presheaf.map (homOfLE le_top).op
    (trace p U hU hcover (q.appTop 1)) = _
  rw [map_one, trace_any_chart p U hU hcover V hV]
  exact AffineTraceCharts.chart_one p V hV basis

end FLT.Mazur.AffineLocallyFreeRelationTrace
