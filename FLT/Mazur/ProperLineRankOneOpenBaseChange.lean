/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineRankOneDirectImage
public import FLT.Mazur.ProperLineIteratedFiberVanishing

/-!
# The constructed geometric rank-one open commutes with base change

On an affine Noetherian new base the independently constructed open is the
literal inverse image of the original open. Its required residue vanishing
is derived from the original family, rather than supplied independently.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
variable {X S T : Scheme.{0}} [IsAffine S] [IsAffine T]
  [IsNoetherianRing Γ(S, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (g : T ⟶ S)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "p" => Limits.pullback.fst f g
local notation "q" => Limits.pullback.snd f g
local notation "h" => IsPullback.of_hasPullback f g
local notation "hV'" => baseChanged_residue_fiber_vanishing h L hL hV

/-- The independently constructed new rank-one open is the original geometric inverse image. -/
theorem properLineRankOneOpen_baseChange :
    properLineRankOneOpen q ((pullback p).obj L) (hL.pullback p) hV' =
      g ⁻¹ᵁ properLineRankOneOpen f L hL hV := by
  ext t
  change (Module.rankAtStalk (R := Γ(T, ⊤))
    (Chow.baseSections ((pullback p).obj L) (q).appTop.hom ⊤) (T.isoSpec.hom t) = 1) ↔ _
  rw [properLineSectionRank_baseChange f L hL hV h]
  have he := congrArg (fun a : T ⟶ Spec Γ(S, ⊤) ↦ a t)
    (Scheme.isoSpec_hom_naturality g)
  change PrimeSpectrum.comap g.appTop.hom (T.isoSpec.hom t) = S.isoSpec.hom (g t) at he
  rw [he]
  rfl

/-- The original open's inclusion pulls back to precisely the newly constructed locus. -/
theorem properLineRankOneOpen_baseChange_range :
    Set.range (Limits.pullback.snd (properLineRankOneOpen f L hL hV).ι g) =
      (properLineRankOneOpen q ((pullback p).obj L) (hL.pullback p) hV' : Set T) := by
  rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι,
    properLineRankOneOpen_baseChange f g L hL hV]

end FLT.Mazur.LineSectionBaseChange
