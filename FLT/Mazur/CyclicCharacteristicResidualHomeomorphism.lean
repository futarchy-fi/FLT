/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicGeometricPointOrbit
public import FLT.Mazur.CyclicCharacteristicResidualChartQuotient

/-!
# The residual characteristic quotient is a homeomorphism

Full residual arrows do not identify further topological points after the
finite quotient. This does not identify sheaves or remove infinitesimal arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The full residual quotient identifies no further points on the finite quotient. -/
theorem finiteProjection_injective : Function.Injective (finiteProjection n b) := by
  intro y z h
  obtain ⟨x, hs, ht⟩ := (finiteProjection_eq_iff n b y z).mp h
  obtain ⟨e, he⟩ := productScheme_point_sameChart_orbit n b x
  have hq := (normalizedQuotientMap_eq_iff_orbit n b
    (productArrowSource n b b x) (productArrowTarget n b b x)).mpr ⟨e, he.symm⟩
  exact hs.symm.trans (hq.trans ht)

/-- The residual map onto the actual characteristic orbit open is injective. -/
theorem finiteToIntegerOpen_injective : Function.Injective (finiteToIntegerOpen n b) := by
  intro y z h
  apply finiteProjection_injective n b
  exact congrArg Subtype.val h

/-- The existing residual quotient map is a homeomorphism, retaining its original topology. -/
theorem finiteToIntegerOpen_isHomeomorph : IsHomeomorph (finiteToIntegerOpen n b) :=
  (isHomeomorph_iff_isQuotientMap_injective).mpr
    ⟨finiteToIntegerOpen_isQuotientMap n b, finiteToIntegerOpen_injective n b⟩

end FLT.Mazur.CyclicCharacteristicOrbit
