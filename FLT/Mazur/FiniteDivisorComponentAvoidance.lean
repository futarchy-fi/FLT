/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSchemeInvertibleSections
public import FLT.Mazur.CartierDivisorComponentRestriction
public import FLT.Mazur.CurveFiberHypotheses
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite divisor support avoids one-dimensional components

The section ring of a finite scheme over a field is Artinian. Its spectrum
has dimension at most zero, so its support cannot contain a subspace of
dimension one. In particular a finite Cartier divisor restricts to every
reduced irreducible component of a pure one-dimensional scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open CoherentDevissage

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Finite schemes over a field have topological dimension at most zero. -/
theorem finiteScheme_dimension_le_zero [IsFinite f] : topologicalKrullDim X ≤ 0 := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have := finiteScheme_globalSections_artinian f
  rw [X.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
  exact topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum Γ(X, ⊤))

variable {I : X.IdealSheafData} [IsFinite (I.subschemeι ≫ f)]

include f

/-- A finite divisor cannot contain a one-dimensional closed subset. -/
theorem finiteDivisor_not_contains_dimension_one (Z : Closeds X)
    (hZ : topologicalKrullDim Z = 1) : ¬ Z ≤ I.support := by
  intro h
  have he := (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le
  have hd : topologicalKrullDim I.support ≤ 0 :=
    finiteScheme_dimension_le_zero (I.subschemeι ≫ f)
  have hh : (1 : WithBot ℕ∞) ≤ 0 := hZ ▸ he.trans hd
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hh

/-- A finite effective divisor is Cartier on each reduced one-dimensional component. -/
theorem finiteDivisor_cartier_on_component (hI : EffectiveCartier I)
    (hX : CurveFiberHypotheses.PureDimensionOne X)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    EffectiveCartier (I.comap (reducedClosedSubschemeι
      ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩)) := by
  exact hI.comap_reducedClosedSubscheme _ hZ.1
    (finiteDivisor_not_contains_dimension_one f _ (hX Z hZ))

end FLT.Mazur.FCurve
