/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineSectionProjective

/-!
# Finite projective line sections after arbitrary affine base change

The new base is unrestricted. Finiteness and projectivity are transported
through the actual section comparison, rather than inferred from Noetherian
hypotheses on that new base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow

variable {P X T S : Scheme.{0}} [IsAffine T] [IsAffine S]
  [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hH : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)))

include h hL hH in
/-- Arbitrary affine base change retains finite projectivity of actual line sections. -/
theorem baseChanged_sections_finite_projective :
    Module.Finite Γ(T, ⊤) (baseSections ((pullback p).obj L) q.appTop.hom ⊤) ∧
    Module.Projective Γ(T, ⊤) (baseSections ((pullback p).obj L) q.appTop.hom ⊤) := by
  let _ := hL.isFinitePresentation
  let _ := Chow.source_isNoetherian (f ≫ S.isoSpec.hom)
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  let _ := proper_sections_finite f L
  let _ := proper_sections_projective f L hL hH
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let e := sectionsEquiv f L hL hH h
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

include h hL hH in
/-- Every stalk over the unrestricted new base is a free module. -/
theorem baseChanged_sections_stalk_free (x : PrimeSpectrum Γ(T, ⊤)) :
    Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule.AtPrime x.asIdeal
        (baseSections ((pullback p).obj L) q.appTop.hom ⊤)) := by
  obtain ⟨hfinite, hprojective⟩ := baseChanged_sections_finite_projective h L hL hH
  let _ := hfinite
  let _ := hprojective
  exact Module.free_of_flat_of_isLocalRing

include h hL in
/-- Positive acyclicity on the original family suffices over every new affine base. -/
theorem baseChanged_acyclic_sections_finite_projective
    (hV : ∀ n, Subsingleton (ModuleH L (n + 1))) :
    Module.Finite Γ(T, ⊤) (baseSections ((pullback p).obj L) q.appTop.hom ⊤) ∧
    Module.Projective Γ(T, ⊤) (baseSections ((pullback p).obj L) q.appTop.hom ⊤) :=
  baseChanged_sections_finite_projective h L hL (positive_flat_of_vanishing f L hV)

end FLT.Mazur.LineSectionBaseChange
