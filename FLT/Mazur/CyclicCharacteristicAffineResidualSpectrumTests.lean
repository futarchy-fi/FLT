/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualPrincipal
public import FLT.Mazur.SchemeRelationInvariantDominant

/-!
# Topological tests for the full affine residual spectrum comparison

The original quotient open is Noetherian and its full residual comparison has
dense image. A residual principal domain is empty exactly when its function is
nilpotent in the full residual ring. Surjectivity and point separation remain
separate requirements for the desired homeomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The original affine source retains the Noetherian topology of its parameter chart. -/
instance invariantAffineChart_noetherianSpace : NoetherianSpace (invariantAffineChart n i) :=
  (invariantAffineInclusion n i).isOpenEmbedding.isInducing.noetherianSpace

/-- The actual orbit topology is Noetherian, before constructing a quotient scheme. -/
instance affineOrbitOpen_noetherianSpace : NoetherianSpace (affineOrbitOpen n i) := by
  let _ : NoetherianSpace (invariantAffineChart n i).toTopCat :=
    invariantAffineChart_noetherianSpace n i
  exact noetherianSpace_of_surjective (affineOrbitProjection n i)
    (affineOrbitProjection n i).hom.continuous (affineOrbitProjection_surjective n i)

/-- Every actual residual principal domain is compact. -/
theorem affineResidualPrincipal_isCompact (s : affineResidualSections n i) :
    IsCompact (affineResidualPrincipal n i s : Set (affineOrbitOpen n i)) :=
  NoetherianSpace.isCompact _

/-- The full residual projection has dense image, using its actual invariant ring inclusion. -/
instance affineResidualProjection_isDominant : IsDominant (affineResidualProjection n i) :=
  SchemeRelationInvariantSpectrum.projection_isDominant _ _

/-- The locally ringed comparison's previously constructed base map has dense image. -/
theorem orbitToResidualSpectrum_denseRange : DenseRange (orbitToResidualSpectrum n i) := by
  have h := (affineResidualProjection n i).denseRange
  have he : orbitToResidualSpectrum n i ∘ affineOrbitProjection n i =
      affineResidualProjection n i := funext (orbitToResidualSpectrum_projection n i)
  rw [← he] at h
  exact h.of_comp

/-- Emptiness is tested on the retained original affine basic open. -/
theorem affineResidualPrincipal_eq_bot_iff_source (s : affineResidualSections n i) :
    affineResidualPrincipal n i s = ⊥ ↔
      (invariantAffineChart n i).basicOpen s.val = ⊥ := by
  constructor
  · intro h
    apply eq_bot_iff.mpr
    intro x hx
    have hx' := (Set.ext_iff.mp (affineResidualPrincipal_preimage n i s) x).mpr hx
    change affineOrbitProjection n i x ∈ affineResidualPrincipal n i s at hx'
    rw [h] at hx'
    exact hx'
  · intro h
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨x, rfl⟩ := affineOrbitProjection_surjective n i z
    have hx := (Set.ext_iff.mp (affineResidualPrincipal_preimage n i s) x).mp hz
    change x ∈ (invariantAffineChart n i).basicOpen s.val at hx
    rw [h] at hx
    exact hx

/-- The actual quotient detects nilpotence in the full residual ring exactly. -/
theorem affineResidualPrincipal_eq_bot_iff (s : affineResidualSections n i) :
    affineResidualPrincipal n i s = ⊥ ↔ IsNilpotent s := by
  rw [affineResidualPrincipal_eq_bot_iff_source,
    ← Scheme.isNilpotent_iff_basicOpen_eq_bot]
  exact IsNilpotent.map_iff (f := (affineResidualSections n i).subtype) Subtype.val_injective

/-- Empty principal domains are detected equally on the quotient and its candidate spectrum. -/
theorem affineResidualPrincipal_eq_bot_iff_spectrum (s : affineResidualSections n i) :
    affineResidualPrincipal n i s = ⊥ ↔ PrimeSpectrum.basicOpen s = ⊥ := by
  rw [affineResidualPrincipal_eq_bot_iff, PrimeSpectrum.basicOpen_eq_bot_iff]

end FLT.Mazur.CyclicCharacteristicOrbit
