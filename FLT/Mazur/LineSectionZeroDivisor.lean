/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineImageCartier
public import FLT.Mazur.LineSectionEvaluation
public import FLT.Mazur.LineTensorInverseComparison

/-!
# The actual zero divisor of a regular line section

The zero ideal is the full image of evaluation from the dual line. Regularity
makes it effective Cartier and identifies its ideal module with the dual line.
Dualizing that identification recovers O(D) as the original line. Nonzero
sections on integral schemes satisfy the required regularity automatically.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{0}} {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))

/-- The zero ideal retains the full evaluation image, not merely its support. -/
def lineSectionZeroIdeal : X.IdealSheafData := by
  have := hL.dual.isFinitePresentation
  exact quasicoherentImageIdeal (lineSectionEvaluation s)

/-- Each affine ideal consists exactly of values of dual sections on the section. -/
lemma lineSectionZeroIdeal_ideal (U : X.affineOpens) :
    (lineSectionZeroIdeal hL s).ideal U =
      LinearMap.range ((lineSectionEvaluation s).val.app (op U.1)).hom := rfl

/-- Membership means actual evaluation, including the nonreduced ideal structure. -/
lemma mem_lineSectionZeroIdeal (U : X.affineOpens) (r : Γ(X, U)) :
    r ∈ (lineSectionZeroIdeal hL s).ideal U ↔
      ∃ φ : Γ(moduleSheafDual L, U.1),
        moduleDualEval L U.1 φ (L.presheaf.map U.1.leTop.op s) = r := by
  change (∃ φ, (lineSectionEvaluation s).app U.1 φ = r) ↔ _
  simp only [lineSectionEvaluation_app]

/-- The actual ideals commute with every affine restriction. -/
lemma lineSectionZeroIdeal_map {U V : X.affineOpens} (h : U ≤ V) :
    ((lineSectionZeroIdeal hL s).ideal V).map
      (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from h)).op).hom =
        (lineSectionZeroIdeal hL s).ideal U :=
  (lineSectionZeroIdeal hL s).map_ideal h

/-- A regular section cuts out an effective Cartier divisor. -/
theorem lineSectionZeroIdeal_effectiveCartier [Mono (globalSectionHom L s)] :
    EffectiveCartier (lineSectionZeroIdeal hL s) := by
  have := hL.dual.isFinitePresentation
  have := lineSectionEvaluation_mono hL s
  exact image_effectiveCartier (lineSectionEvaluation s) hL.dual

/-- The dual line is the actual ideal module of the zero divisor. -/
def lineSectionZeroIdealDualIso [Mono (globalSectionHom L s)] :
    moduleSheafDual L ≅ idealModule (lineSectionZeroIdeal hL s) := by
  have := hL.dual.isFinitePresentation
  have := lineSectionEvaluation_mono hL s
  exact quasicoherentImageIdealIso (lineSectionEvaluation s)

/-- This identification sends evaluation to the actual ideal inclusion. -/
@[reassoc (attr := simp)]
lemma lineSectionZeroIdealDualIso_comp [Mono (globalSectionHom L s)] :
    (lineSectionZeroIdealDualIso hL s).hom ≫ idealModuleι _ = lineSectionEvaluation s := by
  have := hL.dual.isFinitePresentation
  have := lineSectionEvaluation_mono hL s
  exact quasicoherentImageIdealIso_comp (lineSectionEvaluation s)

/-- The positive line of the constructed Cartier divisor is the original line. -/
def lineSectionZeroDivisorLineIso [Mono (globalSectionHom L s)] :
    divisorLineBundle (lineSectionZeroIdeal hL s)
      (lineSectionZeroIdeal_effectiveCartier hL s) ≅ L :=
  moduleSheafDualIso (moduleSheafDual L) (lineSectionZeroIdealDualIso hL s) ≪≫
    lineSheafDoubleDualIso hL

/-- On an integral scheme every nonzero line section gives an actual Cartier zero ideal. -/
theorem nonzero_lineSectionZeroIdeal_effectiveCartier [IsIntegral X] (hs : s ≠ 0) :
    EffectiveCartier (lineSectionZeroIdeal hL s) := by
  have := nonzero_globalSectionHom_mono hL s hs
  exact lineSectionZeroIdeal_effectiveCartier hL s

/-- Recover the original line from the zero divisor of any nonzero section. -/
def nonzeroLineSectionZeroDivisorLineIso [IsIntegral X] (hs : s ≠ 0) :
    divisorLineBundle (lineSectionZeroIdeal hL s)
      (nonzero_lineSectionZeroIdeal_effectiveCartier hL s hs) ≅ L := by
  have := nonzero_globalSectionHom_mono hL s hs
  exact lineSectionZeroDivisorLineIso hL s

end FLT.Mazur.FCurve
