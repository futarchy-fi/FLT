/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts
public import FLT.Mazur.IdealCartierNeighborhood
public import FLT.Mazur.IdealModuleSheaf
public import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Finite presentation of Cartier ideals on affine schemes

Principal Cartier neighborhoods supply rank-one localized ideal modules.
Finite presentation is local on the principal cover, so the whole affine
ideal, and hence its actual ideal-module sections, is finitely presented.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} [IsAffine X]

/-- The ideal of a Cartier divisor on an affine scheme is finitely presented. -/
theorem EffectiveCartier.finitePresentation_ideal {I : X.IdealSheafData}
    (hI : EffectiveCartier I) :
    Module.FinitePresentation Γ(X, ⊤) (I.ideal ⟨⊤, isAffineOpen_top X⟩) := by
  let s : Set Γ(X, ⊤) := {r | CartierChart I (X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) r)}
  have hs : Ideal.span s = ⊤ := by
    apply (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mp
    apply top_unique
    intro x _
    obtain ⟨r, hx, hr⟩ := (effectiveCartier_iff_basicOpen I).mp hI
      ⟨⊤, isAffineOpen_top X⟩ x trivial
    exact Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hx⟩
  let J := I.ideal ⟨⊤, isAffineOpen_top X⟩
  apply Module.FinitePresentation.of_localizationSpan' s hs
    (Rₚ := fun r ↦ Γ(X, X.basicOpen r.1))
    (fun r ↦ Algebra.idealMap Γ(X, X.basicOpen r.1) J)
  intro r
  obtain ⟨a, ha, hIa⟩ := r.2
  have hmap : J.map (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen r.1)) = Ideal.span {a} := by
    rw [← hIa]
    exact I.map_ideal_basicOpen ⟨⊤, isAffineOpen_top X⟩ r.1
  exact Module.FinitePresentation.of_equiv (CartierModule.idealEquiv _ a ha hmap)

/-- Actual global ideal-module sections of an affine Cartier divisor are finitely presented. -/
theorem EffectiveCartier.finitePresentation_sections {I : X.IdealSheafData}
    (hI : EffectiveCartier I) :
    Module.FinitePresentation Γ(X, ⊤) Γ(idealModule I, ⊤) := by
  let := hI.finitePresentation_ideal
  exact Module.FinitePresentation.of_equiv
    (idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top X⟩).symm

end FLT.Mazur.FCurve
