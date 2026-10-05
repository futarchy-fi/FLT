/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafDualEvaluation
public import FLT.Mazur.FiniteSchemeInvertibleSections
public import FLT.Mazur.ClosedPushforwardCohomology

/-!
# Cohomology of line sheaves on finite closed subschemes

The canonical dual supplies the tensor inverse, so no inverse or global
trivialization is an input. The closed pushforward has H⁰ equal in dimension
to the finite scheme length and vanishing positive-degree cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X Z : Scheme}

/-- A line sheaf on a finite scheme has H⁰ dimension equal to the scheme length. -/
theorem finiteScheme_line_h0_finrank (f : Z ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    {L : Z.Modules} (hL : LocallyFreeRankOne L) :
    Module.finrank k (ModuleScalarH f L 0) = finiteSchemeLength f :=
  finiteScheme_invertible_h0_finrank f (moduleSheafDual L) L hL.dual hL
    (lineSheafDualEvaluationIso hL)

variable (i : Z ⟶ X) [IsClosedImmersion i]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsFinite (i ≫ f)]
  {L : Z.Modules} (hL : LocallyFreeRankOne L)

include hL in
/-- Finite closed pushforwards of line sheaves have no positive-degree cohomology. -/
theorem finiteClosed_line_cohomology_subsingleton (n : ℕ) (hn : 0 < n) :
    Subsingleton (ModuleScalarH f ((pushforward i).obj L) n) := by
  have := Chow.source_isNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have := hL.isFinitePresentation
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ f)
  have : Subsingleton (ModuleScalarH (i ≫ f) L n) :=
    affine_moduleH_subsingleton L n hn
  exact (closedPushforwardScalarHEquiv i L f n).injective.subsingleton

include hL in
/-- Closed pushforward preserves the H⁰ dimension of a line on a finite scheme. -/
theorem finiteClosed_line_h0_finrank :
    Module.finrank k (ModuleScalarH f ((pushforward i).obj L) 0) =
      finiteSchemeLength (i ≫ f) := by
  have := Chow.source_isNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have := hL.isFinitePresentation
  exact (closedPushforwardScalarHEquiv i L f 0).finrank_eq.trans
    (finiteScheme_line_h0_finrank (i ≫ f) hL)

end FLT.Mazur.FCurve
