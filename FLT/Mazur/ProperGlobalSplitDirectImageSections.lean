/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGlobalSectionCartier
public import FLT.Mazur.ProperSplitDirectImageSections

/-!
# Retained split maps and relative sections on a non-affine base

The global Cartier criterion converts a locally split direct-image map to
its actual tensor section over a Noetherian affine cover. Both conversions
retain the original twisting line and map, before taking any quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve SplitLineAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} {ι : Type*} (f : X ⟶ S)
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (U : ι → S.Opens) [∀ i, IsAffine (U i).toScheme]
  [∀ i, IsNoetherianRing Γ((U i).toScheme, ⊤)]
  (hV : ∀ i (z : PrimeSpectrum Γ((U i).toScheme, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine
      (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L) z) (n + 1)))
  (hU : iSup U = ⊤)

/-- Recover the original relative section from a split map using a Noetherian affine cover. -/
def SplitDirectImageSection.toGlobalRelative (a : SplitDirectImageSection f L) :
    RelativeSection f L hL := by
  let s := (twistedSectionPushforwardEquiv f L a.baseLine.property).symm a.map
  have hs : LocallySplit (twistedSectionPushforwardEquiv f L a.baseLine.property s) := by
    simpa only [s, Equiv.apply_symm_apply] using a.locallySplit
  obtain ⟨hm, hC⟩ := (ProperGlobalSectionCartier.locallySplit_iff
    f L hL a.baseLine.property s U hV hU).mp hs
  exact ⟨⟨a.baseLine, s, hm⟩, hC.2⟩

/-- The constructed tensor section retains its original direct-image map. -/
lemma SplitDirectImageSection.toGlobalRelative_map (a : SplitDirectImageSection f L) :
    ((a.toGlobalRelative f L hL U hV hU).val.toDirectImage f L).map = a.map :=
  (twistedSectionPushforwardEquiv f L a.baseLine.property).apply_symm_apply a.map

/-- A relative section has a locally split original global direct-image map. -/
def RelativeSection.toGlobalSplitDirectImage (s : RelativeSection f L hL) :
    SplitDirectImageSection f L where
  baseLine := s.val.baseLine
  map := (s.val.toDirectImage f L).map
  locallySplit := (ProperGlobalSectionCartier.locallySplit_iff
    f L hL s.val.baseLine.property s.val.section_ U hV hU).mpr
      ⟨s.val.regular, relativeSection_cartier f L hL s⟩

/-- Converting a relative section and returning retains the section itself. -/
lemma toGlobalRelative_toGlobalSplit (s : RelativeSection f L hL) :
    (s.toGlobalSplitDirectImage f L hL U hV hU).toGlobalRelative f L hL U hV hU = s := by
  apply Subtype.ext
  rcases s with ⟨⟨B, s, hm⟩, hflat⟩
  change (⟨B, (twistedSectionPushforwardEquiv f L B.property).symm
    (twistedSectionPushforwardEquiv f L B.property s), _⟩ : TwistedSection f L) = _
  simp only [Equiv.symm_apply_apply]

/-- Converting a split map and returning retains the original base line and inclusion. -/
lemma toGlobalSplit_toGlobalRelative (a : SplitDirectImageSection f L) :
    (a.toGlobalRelative f L hL U hV hU).toGlobalSplitDirectImage f L hL U hV hU = a := by
  rcases a with ⟨B, a, ha⟩
  change (⟨B, twistedSectionPushforwardEquiv f L B.property
    ((twistedSectionPushforwardEquiv f L B.property).symm a), _⟩ :
      SplitDirectImageSection f L) = _
  simp only [Equiv.apply_symm_apply]

/-- The equivalence over a non-affine base retains the entire original section data. -/
def globalRelativeSplitDirectImageEquiv :
    RelativeSection f L hL ≃ SplitDirectImageSection f L where
  toFun := RelativeSection.toGlobalSplitDirectImage f L hL U hV hU
  invFun := SplitDirectImageSection.toGlobalRelative f L hL U hV hU
  left_inv := toGlobalRelative_toGlobalSplit f L hL U hV hU
  right_inv := toGlobalSplit_toGlobalRelative f L hL U hV hU

end FLT.Mazur.CartierAbel
