/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLinePushforwardTilde

/-!
# Affine base change of the actual proper line direct image

The canonical comparison on sections induces an isomorphism of actual sheaves:
pullback of the direct image agrees with direct image of the pulled-back line.
The normalization diagram uses the affine adjunction counits, so its coefficient
map is the original section comparison and is independent of an affine cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow AffineModuleGlobalSections IncreasingCechCoefficients

variable {P X T S : Scheme.{0}} [IsAffine S] [IsAffine T]
  [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- The canonical section equivalence, as scalar extension in the module category. -/
def residueSectionsIso :
    (ModuleCat.extendScalars g.appTop.hom).obj
      (ModuleCat.of Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)) ≅
        ModuleCat.of Γ(T, ⊤) (baseSections ((pullback p).obj L) q.appTop.hom ⊤) :=
  (LinearEquiv.ofBijective (globalComparison h L)
    (canonical_bijective_of_residue_fibers f L hL hV h)).toModuleIso

/-- The sheaf comparison induced by canonical section base change and reconstruction. -/
def properLinePushforwardBaseChangeIso :
    (pullback g).obj ((pushforward f).obj L) ≅
      (pushforward q).obj ((pullback p).obj L) := by
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ := (hL.pullback p).isFinitePresentation
  exact (pullback g).mapIso (properLinePushforwardTildeIso f L hL).symm ≪≫
    ((AffineQuasiCoherentBaseChange.tildePullbackIso g).app _).symm ≪≫
    (affineTilde T).mapIso (residueSectionsIso h L hL hV) ≪≫
    properPushforwardTildeIso q ((pullback p).obj L)

/-- The reconstruction-normalized sheaf map is exactly tilde of canonical section comparison. -/
lemma properLinePushforwardBaseChangeIso_normalization :
    let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
    let _ := (hL.pullback p).isFinitePresentation
    (AffineQuasiCoherentBaseChange.tildePullbackIso g).app
        (ModuleCat.of Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)) ≪≫
      (pullback g).mapIso (properLinePushforwardTildeIso f L hL) ≪≫
      properLinePushforwardBaseChangeIso h L hL hV =
    (affineTilde T).mapIso (residueSectionsIso h L hL hV) ≪≫
      properPushforwardTildeIso q ((pullback p).obj L) := by
  dsimp only
  ext
  simp [properLinePushforwardBaseChangeIso]

end FLT.Mazur.LineSectionBaseChange
