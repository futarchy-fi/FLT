/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowProductOpenGluing

/-!
# Separated morphisms detected by an affine family of section tests

A family detecting zero global sections of an affine source detects equality
of morphisms over a separated target. The tests need not cover the underlying
topological space, so the criterion applies to all adic thickenings together.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.AffineSeparatedFamilyExt
universe u
variable {T Y S : Scheme.{u}} [IsAffine T] (s : Y ⟶ S) [IsSeparated s]
  {f g : T ⟶ Y} (h : f ≫ s = g ≫ s)

include h

/-- A section-detecting family on the original affine source detects separated morphisms. -/
theorem hom_ext {ι : Type*} (Z : ι → Scheme.{u}) (v : ∀ i, Z i ⟶ T)
    (hv : ∀ x : Γ(T, ⊤), (∀ i, (v i).appTop x = 0) → x = 0)
    (he : ∀ i, v i ≫ f = v i ≫ g) : f = g := by
  let T' : Over S := Over.mk (f ≫ s)
  let Y' : Over S := Over.mk s
  let f' : T' ⟶ Y' := Over.homMk f
  let g' : T' ⟶ Y' := Over.homMk g h.symm
  let _ : IsSeparated Y'.hom := ‹IsSeparated s›
  let _ : IsAffine T'.left := ‹IsAffine T›
  let e := (equalizer.ι f' g').left
  let _ : IsClosedImmersion e := inferInstance
  have hi : IsIso e := by
    apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    apply le_bot_iff.mp
    apply Scheme.IdealSheafData.le_of_isAffine
    intro x hx
    have hx' : e.appTop x = 0 := e.ideal_ker_le _ hx
    change x = 0
    apply hv x
    intro i
    let Z' : Over S := Over.mk (v i ≫ f ≫ s)
    let v' : Z' ⟶ T' := Over.homMk (v i)
    have he' : v' ≫ f' = v' ≫ g' := by ext1; exact he i
    have hf : (equalizer.lift v' he').left ≫ e = v i :=
      congrArg Over.Hom.left (equalizer.lift_ι v' he')
    rw [← hf, Scheme.Hom.comp_appTop]
    change (equalizer.lift v' he').left.appTop (e.appTop x) = 0
    rw [hx', map_zero]
  let _ := hi
  rw [← cancel_epi e]
  exact congrArg Over.Hom.left (equalizer.condition f' g')

end FLT.Mazur.AffineSeparatedFamilyExt
