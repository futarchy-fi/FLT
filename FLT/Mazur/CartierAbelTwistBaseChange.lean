/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelTwistedSections
public import FLT.Mazur.CartierAbelRelativeBaseChange
public import FLT.Mazur.LineSectionZeroIdealPullback

/-!
# Direct geometric pullback of twisted Cartier sections

The base line is pulled to the new test base. The section is pulled through
the actual tensor and square comparisons, independently of divisor recovery.
Its full zero ideal is proved to be the comap of the original ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (L : X.Modules)
variable (hL : LocallyFreeRankOne L)

/-- Pull the retained base line along the new test-base map. -/
def pulledBaseLine (B : SchemePicard.LineBundle S) : SchemePicard.LineBundle T :=
  ⟨(pullback g).obj B.val, B.property.pullback g⟩

/-- The actual tensor comparison includes the sheaf comparison of the cartesian square. -/
def twistBaseChangeIso (B : SchemePicard.LineBundle S) :
    (pullback (Limits.pullback.fst f g)).obj (twist f L B) ≅
      twist (Limits.pullback.snd f g) ((pullback (Limits.pullback.fst f g)).obj L)
        (pulledBaseLine g B) :=
  ModuleLineBundleTensorPullback.tensorIso (Limits.pullback.fst f g) L _ ≪≫
    ModuleSheafTensor.congr (Iso.refl _)
      ((pullbackComp (Limits.pullback.fst f g) f).app B.val ≪≫
        (pullbackCongr Limits.pullback.condition).app B.val ≪≫
        ((pullbackComp (Limits.pullback.snd f g) g).app B.val).symm)

/-- Relative sections impose flatness of the actual zero divisor over the test base. -/
def RelativeSection := {s : TwistedSection f L //
  Flat ((lineSectionZeroIdeal (twist_rankOne f L hL s.baseLine) s.section_).subschemeι ≫ f)}

/-- The zero divisor of a relative twisted section is relative Cartier. -/
theorem relativeSection_cartier (s : RelativeSection f L hL) :
    RelativeEffectiveCartier f
      (lineSectionZeroIdeal (twist_rankOne f L hL s.val.baseLine) s.val.section_) :=
  ⟨lineSectionZeroIdeal_effectiveCartier _ _, s.property⟩

/-- Pull the original section using the actual sheaf comparison. -/
def pulledTwistedSection (s : RelativeSection f L hL) :
    TwistedSection (Limits.pullback.snd f g) ((pullback (Limits.pullback.fst f g)).obj L) where
  baseLine := pulledBaseLine g s.val.baseLine
  section_ := (twistBaseChangeIso f g L s.val.baseLine).hom.app ⊤
    (pullGlobal (Limits.pullback.fst f g) (twist f L s.val.baseLine) s.val.section_)
  regular := by
    let hD := relativeSection_cartier f L hL s
    let _ := relativeCartierIdealPullback f g _ hD
    let _ := pullGlobal_regular_of_zeroIdeal (Limits.pullback.fst f g)
      (twist_rankOne f L hL s.val.baseLine) s.val.section_
      (relativeCartierBaseChange f g _ hD).1
    rw [← globalSectionHom_naturality]
    infer_instance

/-- Pulling the actual twisted section pulls the full ideal, including multiplicities. -/
lemma pulledTwistedSection_zero (s : RelativeSection f L hL) :
    (TwistedSection.toFiber (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g)) (pulledTwistedSection f g L hL s)).val.val =
    (lineSectionZeroIdeal (twist_rankOne f L hL s.val.baseLine) s.val.section_).comap
      (Limits.pullback.fst f g) := by
  let hD := relativeSection_cartier f L hL s
  let _ := relativeCartierIdealPullback f g _ hD
  exact (lineSectionZeroIdeal_eq_of_iso
    ((twist_rankOne f L hL s.val.baseLine).pullback (Limits.pullback.fst f g))
    (twist_rankOne _ _ (hL.pullback (Limits.pullback.fst f g)) _)
    (twistBaseChangeIso f g L s.val.baseLine) _ _ rfl).symm.trans
      (lineSectionZeroIdeal_pullGlobal (Limits.pullback.fst f g)
        (twist_rankOne f L hL s.val.baseLine) s.val.section_
        (relativeCartierBaseChange f g _ hD).1)

/-- The direct pulled section is again relative over the unrestricted new test base. -/
def relativeSectionBaseChange (s : RelativeSection f L hL) :
    RelativeSection (Limits.pullback.snd f g) ((pullback (Limits.pullback.fst f g)).obj L)
      (hL.pullback (Limits.pullback.fst f g)) := by
  refine ⟨pulledTwistedSection f g L hL s, ?_⟩
  change Flat ((TwistedSection.toFiber _ _ (hL.pullback (Limits.pullback.fst f g))
    (pulledTwistedSection f g L hL s)).val.val.subschemeι ≫ Limits.pullback.snd f g)
  rw [pulledTwistedSection_zero]
  exact (relativeSection_cartier f L hL s).flat_baseChange g

/-- The original relative section determines a point in the actual relative Abel fiber. -/
def relativeSectionToFiber (s : RelativeSection f L hL) : RelativeFiber f L hL :=
  ⟨TwistedSection.toFiber f L hL s.val, s.property⟩

/-- Direct sheaf-section pullback agrees with the independent divisor-fiber pullback. -/
theorem relativeSectionToFiber_baseChange (s : RelativeSection f L hL) :
    relativeSectionToFiber _ _ _ (relativeSectionBaseChange f g L hL s) =
      fiberBaseChange f g L hL (relativeSectionToFiber f L hL s) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact pulledTwistedSection_zero f g L hL s

end FLT.Mazur.CartierAbel
