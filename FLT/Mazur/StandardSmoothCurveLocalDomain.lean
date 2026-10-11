/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DomainLocalizationNeighborhood
public import FLT.Mazur.EtaleCurveLocalDomain
public import FLT.Mazur.SectionDivisors
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Domain neighborhoods on standard smooth field curves

The existing étale polynomial coordinate gives a domain at every prime.
Noetherianity then spreads this to a principal neighborhood of that same prime.
The field is arbitrary; no algebraic closure or rationality assumption is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve

universe u
variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
  [hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 1 K B]

include hSmooth

/-- Local rings of standard smooth relative curves over a field are domains. -/
theorem isDomain_atPrime_of_standardSmooth_curve (q : Ideal B) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) := by
  obtain ⟨g, hg⟩ := exists_etale_polynomial_coordinate (R := K) (B := B)
  let _ := g.toAlgebra
  let _ : Algebra.Etale (Polynomial K) B := hg
  exact isDomain_atPrime_of_etale_pid (Polynomial K) B q

/-- Each point of a standard smooth field curve has a principal domain neighborhood. -/
theorem exists_domain_away_of_standardSmooth_curve (q : Ideal B) [q.IsPrime] :
    ∃ r : B, r ∉ q ∧ IsDomain (Localization.Away r) := by
  let _ : Algebra.IsStandardSmooth K B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  let _ := isDomain_atPrime_of_standardSmooth_curve (K := K) q
  exact exists_domain_away_of_isDomain_atPrime q

end FLT.Mazur.FCurve
