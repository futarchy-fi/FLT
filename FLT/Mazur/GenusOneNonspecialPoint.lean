/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveNonspecialDivisor
public import FLT.Mazur.FiniteDivisorLengthOne
public import FLT.Mazur.PointedCurveLargeDegree

/-!
# An actual nonspecial point on a geometric genus-one curve

The existing nonspecial divisor has length equal to the genus. In genus one,
its entire ideal is the ideal of a rational point. A given original point
supplies ampleness; no Weierstrass equation or low-degree vanishing is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  (hd : topologicalKrullDim X = 1) (hc : HasConstantGlobalSections f)

/-- A genus-one curve with an ample line has a nonspecial rational-point divisor. -/
theorem genusOne_exists_nonspecial_point (hg : curveGenus f hd hc = 1)
    {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ (s : Spec (.of k) ⟶ X) (hI : EffectiveCartier s.ker),
      s ≫ f = 𝟙 _ ∧ Subsingleton (ModuleScalarH f (divisorLineBundle s.ker hI) 1) ∧
        Module.finrank k (ModuleScalarH f (divisorLineBundle s.ker hI) 0) = 1 := by
  obtain ⟨I, hI, hfin, hz, hr, hlen⟩ :=
    exists_nonspecial_effective_divisor_genus f hd hc hB
  let _ := hfin
  obtain ⟨s, hs, he⟩ := (divisorFieldLength_one_iff_section f I).mp (hlen.trans hg)
  subst I
  exact ⟨s, hI, hs, hz, hr⟩

/-- An original rational point suffices to construct a nonspecial rational point. -/
theorem pointed_genusOne_exists_nonspecial_point (hg : curveGenus f hd hc = 1)
    (o : Spec (.of k) ⟶ X) (ho : o ≫ f = 𝟙 _) :
    ∃ (s : Spec (.of k) ⟶ X) (hI : EffectiveCartier s.ker),
      s ≫ f = 𝟙 _ ∧ Subsingleton (ModuleScalarH f (divisorLineBundle s.ker hI) 1) ∧
        Module.finrank k (ModuleScalarH f (divisorLineBundle s.ker hI) 0) = 1 := by
  obtain ⟨B, hB⟩ := pointedCurve_exists_ample_line f hd.le o ho
  exact genusOne_exists_nonspecial_point f hd hc hg hB

end FLT.Mazur.FCurve
