/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNonspecialLine
public import FLT.Mazur.LineSectionZeroDivisor
public import FLT.Mazur.IntegralCurveCartierFinite
public import FLT.Mazur.CurveRiemannRochEuler
public import FLT.Mazur.FiniteDivisorCohomology

/-!
# Existence of a full nonspecial effective divisor on a geometric curve

The unique section line constructed by successive point conditions gives an
actual Cartier zero ideal. Its divisor line has vanishing H¹ and H⁰ of dimension
one. Riemann–Roch identifies the full finite divisor's length with the genus.
This is geometric-field existence; relative spreading and fppf coverage are separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

/-- An ample smooth proper geometric curve has a full finite nonspecial divisor. -/
theorem exists_nonspecial_effective_divisor {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ (I : X.IdealSheafData) (hI : EffectiveCartier I), IsFinite (I.subschemeι ≫ f) ∧
      Subsingleton (ModuleScalarH f (divisorLineBundle I hI) 1) ∧
      Module.finrank k (ModuleScalarH f (divisorLineBundle I hI) 0) = 1 := by
  obtain ⟨L, hL, hz, hr⟩ := exists_acyclic_rank_one_line_of_ample f hB
  obtain ⟨s, hs⟩ := exists_nonzero_section_of_h0_pos f L (by omega)
  let I := lineSectionZeroIdeal hL s
  let hI := nonzero_lineSectionZeroIdeal_effectiveCartier hL s hs
  let e : divisorLineBundle I hI ≅ L := nonzeroLineSectionZeroDivisorLineIso hL s hs
  let _ : Subsingleton (ModuleH L 1) := hz
  have hv : Subsingleton (ModuleScalarH f (divisorLineBundle I hI) 1) :=
    moduleH_subsingleton_of_iso e 1
  exact ⟨I, hI, hI.isFinite_of_integral_smoothCurve f, hv,
    ((moduleScalarHFunctor f 0).mapIso e).toLinearEquiv.finrank_eq.trans hr⟩

/-- The full finite nonspecial divisor has length equal to the actual curve genus. -/
theorem exists_nonspecial_effective_divisor_genus
    (hd : topologicalKrullDim X = 1) (hc : HasConstantGlobalSections f)
    {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ (I : X.IdealSheafData) (hI : EffectiveCartier I), IsFinite (I.subschemeι ≫ f) ∧
      Subsingleton (ModuleScalarH f (divisorLineBundle I hI) 1) ∧
      Module.finrank k (ModuleScalarH f (divisorLineBundle I hI) 0) = 1 ∧
      divisorFieldLength f I = curveGenus f hd hc := by
  obtain ⟨I, hI, hf, hz, hr⟩ := exists_nonspecial_effective_divisor f hB
  let _ := hf
  let _ := hz
  have he := curve_h0_eq_of_h1_vanishing f hd hc (divisorLineBundle I hI)
  rw [hr, divisor_degree_eq_fieldLength f hI] at he
  exact ⟨I, hI, hf, hz, hr, by omega⟩

end FLT.Mazur.FCurve
