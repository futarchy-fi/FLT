/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleSectionCoverPullback
public import FLT.Mazur.FiniteNeighborhoodAffineOpens
public import FLT.Mazur.SectionProjectiveFiniteNeighborhood

/-!
# Ampleness from a finite section morphism over a base neighborhood

The standard projective charts pull back to the actual generator opens.
Finiteness over an affine base open makes the restricted opens affine,
and their positive-power sections therefore prove ampleness there.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.FCurve

open ProjectiveSpace

variable {X : Scheme.{0}} [CompactSpace X] {L : X.Modules}
  (hL : LocallyFreeRankOne L) {R : Type} [CommRing R] {n : ℕ} (hn : 0 < n)
  (d : ℕ) (t : Fin (d + 1) → Γ(tensorPower L n, ⊤))
  (ht : ⨆ i, sectionGeneratorOpen (tensorPower L n) (t i) = ⊤)
  (r : R →+* Γ(X, ⊤)) (U : (Spec (.of R)).Opens) (hU : IsAffineOpen U)

include hL hn hU

/-- A finite projective section morphism proves ampleness on its affine base restriction. -/
theorem ampleLineBundle_of_finite_sectionProjectiveMorphism
    [IsFinite ((sectionProjectiveMorphism (tensorPower L n) d t ht r) ∣_
      (baseProjection R (Fin (d + 1)) ⁻¹ᵁ U))] :
    AmpleLineBundle ((pullback
      ((sectionProjectiveMorphism (tensorPower L n) d t ht r) ⁻¹ᵁ
        (baseProjection R (Fin (d + 1)) ⁻¹ᵁ U)).ι).obj L) := by
  let g := sectionProjectiveMorphism (tensorPower L n) d t ht r
  let p := baseProjection R (Fin (d + 1))
  let j := (g ⁻¹ᵁ (p ⁻¹ᵁ U)).ι
  have hj : IsAffineHom j := by
    have ha := Approximation.isAffineHom_baseOpen_inclusion (g ≫ p) U hU
    simpa only [Scheme.Hom.comp_preimage] using ha
  let _ : CompactSpace (g ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace j
  apply ampleLineBundle_pullback_of_section_cover hL j hn t ht
  intro i
  have ha := Approximation.isAffineOpen_chart_preimage_finite_restrict g p U hU
    (chart R (Fin (d + 1)) i) (.of_isIso (chartIso R (Fin (d + 1)) i).hom)
  rwa [sectionProjectiveMorphism_preimage_chart] at ha

end FLT.Mazur.FCurve
