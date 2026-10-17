/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalDivisorLine
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Canonical sections in the original finite coefficient comparison

The existing positive marking-line comparison preserves its actual divisor
section for arbitrary coefficient maps, without flatness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.PolygonInfinitesimal
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme parameterProjection markingDivisor
  divisorLineBundle markingLineParameterIso
variable {R S : Type u} [CommRing R] [CommRing S]
  (t : R) [Fact (IsNilpotent t)] (n : ℕ) (h : 2 ≤ n)
  (φ : R →+* S) (s : S) [Fact (IsNilpotent s)] (ht : φ t = s) (a : Fin n → Rˣ)

/-- The original coefficient comparison preserves the canonical section of the entire sum. -/
theorem markingLineParameterIso_section :
    DivisorLineSectionCompatible (parameterProjection φ t s ht n h)
      (markingDivisor_cartier R t n h a).1
      (markingDivisor_cartier S s n h (fun i ↦ Units.map φ.toMonoidHom (a i))).1
      (markingLineParameterIso t n h φ s ht a) := by
  rw [markingLineParameterIso]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Every power of the original finite coefficient comparison retains its powered section. -/
theorem markingLineParameterIso_power_section (d : ℕ) :
    DivisorLinePowerSectionCompatible (parameterProjection φ t s ht n h)
      (markingDivisor_cartier R t n h a).1
      (markingDivisor_cartier S s n h (fun i ↦ Units.map φ.toMonoidHom (a i))).1
      (markingLineParameterIso t n h φ s ht a) d :=
  (markingLineParameterIso_section t n h φ s ht a).tensorPower_section d

end FLT.Mazur.PolygonInfinitesimal
