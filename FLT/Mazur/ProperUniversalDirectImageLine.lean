/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineArbitraryBaseChange
public import FLT.Mazur.ProperLinePushforwardLocalFree
public import FLT.Mazur.DualAtlasUniversalLine
public import FLT.Mazur.DualAtlasSectionTransport

/-!
# The universal line in the actual proper direct image

The universal retained line on the original dual projective atlas is
transported into the direct image of the actual base-changed family.
Its inclusion uses the independently defined base-change mate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange DualAtlasLineQuotient LocallyFreeDualProjectiveAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "p" => Limits.pullback.fst f π
local notation "q" => Limits.pullback.snd f π

/-- The actual universal retained line inside the proper direct image over the atlas. -/
@[irreducible] def line : Line ((pushforward q).obj ((pullback p).obj L)) :=
  (DualAtlasUniversalLine.universalLine M hM).changeAmbient
    (properLineArbitraryBaseChangeIso (IsPullback.of_hasPullback f π) L hL hV)

/-- Transport into the direct image preserves the original universal source line. -/
lemma line_source :
    (line f L hL hV).source = (DualAtlasUniversalLine.universalLine M hM).source := by
  unfold line
  rfl

/-- The actual universal inclusion is its original inclusion followed by the actual mate. -/
lemma line_inclusion :
    (line f L hL hV).inclusion =
      eqToHom (line_source f L hL hV) ≫
        (DualAtlasUniversalLine.universalLine M hM).inclusion ≫
          DirectImageBaseChange.comparison p q f π Limits.pullback.condition.symm L := by
  unfold line
  erw [eqToHom_refl]
  · simp only [Line.changeAmbient, Category.id_comp, properLineArbitraryBaseChangeIso_hom]
  · rfl

/-- Transporting back recovers the original universal atlas section and hence its identity map. -/
lemma line_atlas_identity :
    (toSection _ ((hM).pullback π) ((line f L hL hV).changeAmbient
      (properLineArbitraryBaseChangeIso (IsPullback.of_hasPullback f π) L hL hV).symm)).val ≫
        DualAtlasBaseChangeCharts.map π M hM = 𝟙 _ := by
  have he : (line f L hL hV).changeAmbient
      (properLineArbitraryBaseChangeIso (IsPullback.of_hasPullback f π) L hL hV).symm =
        DualAtlasUniversalLine.universalLine M hM := by
    unfold line
    simp only [Line.changeAmbient, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [he]
  exact DualAtlasUniversalLine.universalLine_map M hM

end FLT.Mazur.ProperUniversalDirectImage
