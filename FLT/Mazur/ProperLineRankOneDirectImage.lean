/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveRankOneTrivialization
public import FLT.Mazur.ProperLineSectionRankLocus
public import FLT.Mazur.ProperLineArbitraryBaseChange

/-!
# The actual proper direct image on its rank-one open

The section rank defines an open subscheme of the original base. Every test
scheme mapping into this open has an actual rank-one direct image, obtained
from principal coefficient frames and the original base-change mate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- The rank-one locus as an actual open of the original geometric base. -/
def properLineRankOneOpen : S.Opens :=
  S.isoSpec.hom ⁻¹ᵁ properLineSectionRankOpen f L hL hV 1

/-- The open is defined by the original section module, evaluated at the original point. -/
lemma mem_properLineRankOneOpen (s : S) :
    s ∈ properLineRankOneOpen f L hL hV ↔
      Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)
        (S.isoSpec.hom s) = 1 := Iff.rfl

/-- Mapping into the rank-one open constructs local frames on an arbitrary test scheme. -/
theorem properLinePullback_rankOne {T : Scheme.{0}} (g : T ⟶ S)
    (hg : ∀ t : T, g t ∈ properLineRankOneOpen f L hL hV) :
    LocallyFreeRankOne ((pullback g).obj ((pushforward f).obj L)) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := projective_sections_of_residue_fibers f L hL hV
  let M := ModuleCat.of Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)
  have hm := finiteProjective_tilde_pullback_rankOne M (g ≫ S.isoSpec.hom) hg
  exact hm.of_iso (((pullbackComp g S.isoSpec.hom).app (tilde M)).symm ≪≫
    (pullback g).mapIso (properLinePushforwardTildeIso f L hL))

/-- The original direct image restricts to an actual line bundle on the constructed open. -/
theorem properLineRankOneOpen_line :
    LocallyFreeRankOne ((pullback (properLineRankOneOpen f L hL hV).ι).obj
      ((pushforward f).obj L)) :=
  properLinePullback_rankOne f L hL hV _ (fun t ↦ t.property)

/-- The original base-change mate identifies each test family's direct image with a line. -/
theorem properLineBaseChanged_rankOne {P T : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g)
    (hg : ∀ t : T, g t ∈ properLineRankOneOpen f L hL hV) :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) :=
  (properLinePullback_rankOne f L hL hV g hg).of_iso
    (properLineArbitraryBaseChangeIso h L hL hV)

/-- In particular the family over the actual rank-one open has a line as its direct image. -/
theorem properLineRankOneOpen_directImage :
    LocallyFreeRankOne
      ((pushforward (Limits.pullback.snd f (properLineRankOneOpen f L hL hV).ι)).obj
        ((pullback (Limits.pullback.fst f (properLineRankOneOpen f L hL hV).ι)).obj L)) :=
  properLineBaseChanged_rankOne f L hL hV (IsPullback.of_hasPullback _ _)
    (fun t ↦ t.property)

end FLT.Mazur.LineSectionBaseChange
