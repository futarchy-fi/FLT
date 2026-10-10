/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLinePushforwardTilde
public import FLT.Mazur.FiniteProjectiveTildeLocal
public import FLT.Mazur.LineSectionProjectiveBaseChange

/-!
# Finite free charts for proper line direct images

The actual pushforward is locally finite free whenever its section module is
finite projective. Residue-fiber vanishing constructs these hypotheses, and
the result persists over arbitrary affine new bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow

variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f]

/-- Finite projective sections give finite free charts of the actual proper direct image. -/
theorem properPushforward_locallyFiniteFree (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(S, ⊤) (baseSections M f.appTop.hom ⊤)]
    [Module.Projective Γ(S, ⊤) (baseSections M f.appTop.hom ⊤)] :
    LocallyFiniteFree ((pushforward f).obj M) :=
  (finiteProjective_affineTilde_locallyFiniteFree S
    (ModuleCat.of Γ(S, ⊤) (baseSections M f.appTop.hom ⊤))).of_iso
      (properPushforwardTildeIso f M)

variable [IsNoetherianRing Γ(S, ⊤)] [Flat f] (L : X.Modules)
  (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include hL hV in
/-- Residue-fiber vanishing produces actual finite free direct-image charts. -/
theorem properLinePushforward_locallyFiniteFree :
    LocallyFiniteFree ((pushforward f).obj L) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := projective_sections_of_residue_fibers f L hL hV
  exact properPushforward_locallyFiniteFree f L

include hL hV in
/-- The direct image after any affine base change has finite free charts as well. -/
theorem baseChanged_linePushforward_locallyFiniteFree {P T : Scheme.{0}} [IsAffine T]
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    LocallyFiniteFree ((pushforward q).obj ((pullback p).obj L)) := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ := (hL.pullback p).isFinitePresentation
  obtain ⟨hfinite, hprojective⟩ := baseChanged_acyclic_sections_finite_projective h L hL
    (positive_vanishing_of_residue_fibers f L hL hV)
  let _ := hfinite
  let _ := hprojective
  exact properPushforward_locallyFiniteFree q ((pullback p).obj L)

end FLT.Mazur.LineSectionBaseChange
