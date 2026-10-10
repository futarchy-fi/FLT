/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartResidueEquation
public import FLT.Mazur.AffineSectionMonicity
public import FLT.Mazur.LineSectionFrameZeroIdeal
public import FLT.Mazur.RelativeSums

/-!
# The affine relative Cartier converse for framed sections

For a flat morphism between Noetherian affine schemes, monicity of the actual
section on residue tensor charts constructs total monicity and a flat full
zero subscheme. The quotient and ideal are derived from the original frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.AffineFiberwiseSectionCartier
open FCurve AffineChartResidueEquation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsAffine X] [IsAffine S]
  [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [Flat f] {L : X.Modules}

/-- Residue regularity constructs both the section embedding and its relative Cartier divisor. -/
theorem relativeCartier (hL : LocallyFreeRankOne L) (e : L ≅ structureModule X)
    (s : Γ(L, ⊤))
    (hs : let _ := f.appTop.hom.toAlgebra
      ∀ (p : Ideal Γ(S, ⊤)) [p.IsPrime], Mono (globalSectionHom _
        (pullGlobal (chartMap (X := X) (Algebra.TensorProduct.includeRight :
          Γ(X, ⊤) →ₐ[Γ(S, ⊤)] p.ResidueField ⊗[Γ(S, ⊤)] Γ(X, ⊤)).toRingHom) L s))) :
    Mono (globalSectionHom L s) ∧ RelativeEffectiveCartier f (lineSectionZeroIdeal hL s) := by
  let _ := f.appTop.hom.toAlgebra
  let _ : Module.Flat Γ(S, ⊤) Γ(X, ⊤) := f.flat_appTop
  obtain ⟨hr, hq⟩ := regular_and_flat e s hs
  have hm := AffineSectionMonicity.mono_of_regular e s hr
  refine ⟨hm, lineSectionZeroIdeal_effectiveCartier hL s, ?_⟩
  apply flat_subscheme_of_chart_quotients
  intro x
  refine ⟨⟨⊤, isAffineOpen_top S⟩, ⟨⊤, isAffineOpen_top X⟩, trivial, le_top,
    e.hom.app ⊤ s, LineSectionFrameZeroIdeal.top_ideal_eq_span hL e s, ?_⟩
  have hf := RingHom.flat_algebraMap_iff.mpr hq
  convert hf using 1
  ext r
  change Ideal.Quotient.mk _ ((f.appLE ⊤ ⊤ le_top) r) =
    Ideal.Quotient.mk _ (f.appTop r)
  congr 1
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

end FLT.Mazur.AffineFiberwiseSectionCartier
