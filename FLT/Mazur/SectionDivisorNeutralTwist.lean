/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelTwistBaseChange
public import FLT.Mazur.SectionPointPowerBaseChange

/-!
# The original section divisor with the neutral base twist

The canonical divisor section defines a relative Cartier section with the
structure module as its base line. Its full zero ideal is the original
section kernel, and removing the neutral twist recovers the canonical section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open CartierAbel ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle

variable {X S : Scheme} (f : X ⟶ S)

/-- The neutral base line, retaining its actual structure sheaf. -/
def sectionNeutralBaseLine : SchemePicard.LineBundle S :=
  ⟨structureModule S, structureModule_locallyFreeRankOne⟩

/-- Remove the pulled-back neutral tensor factor by the canonical unit maps. -/
def sectionNeutralTwistIso (L : X.Modules) :
    twist f L sectionNeutralBaseLine ≅ L :=
  ModuleSheafTensor.congr (Iso.refl L) (modulePullbackUnitIso f) ≪≫ rightUnitor L

variable (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  (hI : EffectiveCartier s.ker)

/-- The original canonical divisor section, expressed with the neutral base twist. -/
def sectionDivisorNeutralSection : TwistedSection f (divisorLineBundle s.ker hI) :=
  sectionOfDivisor f (divisorLineBundle s.ker hI) ⟨s.ker, hI⟩ sectionNeutralBaseLine
    (sectionNeutralTwistIso f (divisorLineBundle s.ker hI)).symm

/-- Removing the neutral twist gives exactly the original canonical section. -/
theorem sectionDivisorNeutralSection_untwist :
    (sectionNeutralTwistIso f (divisorLineBundle s.ker hI)).hom.app ⊤
      (sectionDivisorNeutralSection f s hI).section_ = divisorSection hI ⊤ := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun a ↦ a.app ⊤)
      (sectionNeutralTwistIso f (divisorLineBundle s.ker hI)).inv_hom_id) _

/-- The full scheme-theoretic zero ideal is the original section ideal. -/
theorem sectionDivisorNeutralSection_zero :
    lineSectionZeroIdeal
      (twist_rankOne f _ hI.divisorLineBundle_locallyFreeRankOne sectionNeutralBaseLine)
      (sectionDivisorNeutralSection f s hI).section_ = s.ker :=
  congrArg Subtype.val (sectionOfDivisor_zero f _ hI.divisorLineBundle_locallyFreeRankOne
    ⟨s.ker, hI⟩ sectionNeutralBaseLine
    (sectionNeutralTwistIso f (divisorLineBundle s.ker hI)).symm)

variable [IsSeparated f]

/-- Flatness of the actual section image makes the original canonical section relative. -/
def sectionDivisorRelativeSection :
    RelativeSection f (divisorLineBundle s.ker hI) hI.divisorLineBundle_locallyFreeRankOne := by
  refine ⟨sectionDivisorNeutralSection f s hI, ?_⟩
  rw [sectionDivisorNeutralSection_zero]
  exact flat_sectionImage f s hs

end FLT.Mazur.FCurve
