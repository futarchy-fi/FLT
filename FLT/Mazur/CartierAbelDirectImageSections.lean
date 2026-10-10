/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelTwistedSections
public import FLT.Mazur.TwistedSectionRegularity

/-!
# Direct-image morphisms representing actual Cartier Abel fibers

Retaining the base line, twisted regular sections are equivalent to morphisms
from its dual to the actual direct image whose counit adjoint is monic.
Every actual Cartier Abel fiber point is the zero ideal of such a morphism.
Local splitting on the base is not assumed or claimed here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- A retained base line and a direct-image morphism with regular total-space adjoint. -/
structure DirectImageSection where
  /-- The original twisting line on the test base. -/
  baseLine : SchemePicard.LineBundle S
  /-- The actual map from its intrinsic dual to the actual sheaf direct image. -/
  map : moduleSheafDual baseLine.val ⟶ (pushforward f).obj L
  /-- Regularity of its independently defined counit adjoint on the total space. -/
  regular : Mono ((pullback f).map map ≫ (pullbackPushforwardAdjunction f).counit.app L)

/-- Tensor duality and the sheaf adjunction applied to a retained twisted section. -/
def TwistedSection.toDirectImage (s : TwistedSection f L) : DirectImageSection f L where
  baseLine := s.baseLine
  map := twistedSectionPushforwardEquiv f L s.baseLine.property s.section_
  regular := (twistedSectionPushforwardEquiv_regular_iff f L
    s.baseLine.property s.section_).mpr s.regular

/-- Recover the original tensor section from its direct-image morphism. -/
def DirectImageSection.toTwisted (a : DirectImageSection f L) : TwistedSection f L where
  baseLine := a.baseLine
  section_ := (twistedSectionPushforwardEquiv f L a.baseLine.property).symm a.map
  regular := (twistedSectionPushforwardEquiv_symm_regular_iff f L
    a.baseLine.property a.map).mpr a.regular

/-- The correspondence retains every base line and the actual regular section. -/
def directImageSectionEquiv : TwistedSection f L ≃ DirectImageSection f L where
  toFun := TwistedSection.toDirectImage f L
  invFun := DirectImageSection.toTwisted f L
  left_inv s := by
    cases s
    simp only [TwistedSection.toDirectImage, DirectImageSection.toTwisted,
      Equiv.symm_apply_apply]
  right_inv a := by
    cases a
    simp only [TwistedSection.toDirectImage, DirectImageSection.toTwisted,
      Equiv.apply_symm_apply]

variable (hL : LocallyFreeRankOne L)

/-- The full zero ideal of the recovered section is an actual Abel fiber point. -/
def DirectImageSection.toFiber (a : DirectImageSection f L) : Fiber f L hL :=
  TwistedSection.toFiber f L hL (a.toTwisted f L)

/-- Converting a section to a direct-image map retains its full Cartier zero ideal. -/
lemma toDirectImage_toFiber (s : TwistedSection f L) :
    DirectImageSection.toFiber f L hL (s.toDirectImage f L) =
      TwistedSection.toFiber f L hL s := by
  change TwistedSection.toFiber f L hL
    ((directImageSectionEquiv f L).symm (directImageSectionEquiv f L s)) = _
  rw [Equiv.symm_apply_apply]

/-- Every actual Abel fiber divisor is represented by a retained direct-image morphism. -/
theorem directImageSection_toFiber_surjective :
    Function.Surjective (DirectImageSection.toFiber f L hL) := by
  intro D
  obtain ⟨s, hs⟩ := twistedSection_toFiber_surjective f L hL D
  exact ⟨s.toDirectImage f L, (toDirectImage_toFiber f L hL s).trans hs⟩

end FLT.Mazur.CartierAbel
