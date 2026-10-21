/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import FLT.Mazur.CartierImmersionFinitePresentation

/-!
# Finite equations of closed ideal subschemes

A finitely presented closed immersion has finitely generated ideals on every
ambient affine open. Arbitrary pullback of a Cartier divisor therefore has
finite ideal equations, even when its pulled equation is a zero divisor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IdealSheafFiniteEquations
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme} (I : Y.IdealSheafData)

/-- A finitely presented closed immersion gives finite affine ideal generators. -/
theorem ideal_fg [LocallyOfFinitePresentation I.subschemeι] (U : Y.affineOpens) :
    (I.ideal U).FG := by
  let r := (I.subschemeι.app U.1).hom
  let _ := r.toAlgebra
  have hp := I.subschemeι.finitePresentation_appLE U.2 (U.2.preimage I.subschemeι) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hp
  let _ : Algebra.FinitePresentation Γ(Y, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) := hp
  have h := Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(Y, U.1) Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1))
    (I.subschemeι.app_surjective U.1 U.2)
  change (RingHom.ker r).FG at h
  rwa [I.ker_subschemeι_app U] at h

/-- Pulling a Cartier divisor along any map retains finite equations on every affine open. -/
theorem cartier_comap_ideal_fg (hI : FCurve.EffectiveCartier I) (f : X ⟶ Y)
    (U : X.affineOpens) : ((I.comap f).ideal U).FG := by
  let _ := hI.locallyOfFinitePresentation_subschemeι
  let _ : LocallyOfFinitePresentation (I.comap f).subschemeι := by
    rw [← I.comapIso_hom_fst f]
    infer_instance
  exact ideal_fg (I.comap f) U

end FLT.Mazur.IdealSheafFiniteEquations
