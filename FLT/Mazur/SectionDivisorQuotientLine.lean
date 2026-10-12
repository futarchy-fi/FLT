/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTwistedProjection
public import FLT.Mazur.DivisorPowerLeadingClass
public import FLT.Mazur.IsomorphicClosedPullback
public import FLT.Mazur.SectionDivisors
public import Mathlib.Tactic.IrreducibleDef

/-!
# The actual section-divisor quotient is a line on the base

The section image comparison identifies the twisted divisor quotient with
the pushforward of the original line restricted along the section. The
comparison preserves the actual quotient map, not just its isomorphism class.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] divisorLineBundle

variable {X S : Scheme} (f : X ⟶ S) [IsSeparated f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (hI : EffectiveCartier s.ker)

/-- The original degree-m line along the marked section, with no chosen frame. -/
def sectionPoleLine (m : ℕ) : S.Modules :=
  (pullback s).obj (tensorPower (divisorLineBundle s.ker hI) m)

/-- Every section pole line is locally free of rank one on the actual base. -/
theorem sectionPoleLine_rankOne (m : ℕ) :
    LocallyFreeRankOne (sectionPoleLine s hI m) :=
  (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m).pullback s

/-- The image presentation changes to the original section over the curve. -/
lemma sectionImageIso_inv_embedding :
    (sectionImageIso f s hs).inv ≫ s.ker.subschemeι = s := by
  rw [← sectionImageIso_hom_section f s hs, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- Change the image presentation for an arbitrary coefficient line. -/
def sectionTwistedQuotientIso (L : X.Modules) (hL : LocallyFreeRankOne L) :
    (divisorTwistedComplex hI L).X₃ ≅
      (pushforward s).obj ((pullback s).obj
        (ModuleSheafTensor.tensor (divisorLineBundle s.ker hI) L)) :=
  divisorTwistedQuotientIso hI L hL ≪≫
    IsomorphicClosedPullback.overIso (sectionImageIso f s hs).symm s.ker.subschemeι
      (ModuleSheafTensor.tensor (divisorLineBundle s.ker hI) L) s
      (sectionImageIso_inv_embedding f s hs)

/-- Changing the image presentation preserves the original quotient morphism. -/
theorem sectionTwistedQuotientIso_projection (L : X.Modules) (hL : LocallyFreeRankOne L) :
    (divisorTwistedComplex hI L).g ≫ (sectionTwistedQuotientIso f s hs hI L hL).hom =
      (pullbackPushforwardAdjunction s).unit.app
        (ModuleSheafTensor.tensor (divisorLineBundle s.ker hI) L) := by
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, divisorTwistedQuotientIso_projection]
  exact IsomorphicClosedPullback.unit_overIso _ _ _ _ _

/-- The actual quotient is the closed pushforward of the base pole line. -/
irreducible_def sectionDivisorQuotientIso (m : ℕ) :
    (divisorTwistedComplex hI (tensorPower (divisorLineBundle s.ker hI) m)).X₃ ≅
      (pushforward s).obj (sectionPoleLine s hI (m + 1)) :=
  sectionTwistedQuotientIso f s hs hI _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)

/-- The quotient map becomes the original restriction to the section. -/
theorem sectionDivisorQuotientIso_projection (m : ℕ) :
    (divisorTwistedComplex hI (tensorPower (divisorLineBundle s.ker hI) m)).g ≫
      (sectionDivisorQuotientIso f s hs hI m).hom =
        (pullbackPushforwardAdjunction s).unit.app
          (tensorPower (divisorLineBundle s.ker hI) (m + 1)) := by
  rw [sectionDivisorQuotientIso_def]
  exact sectionTwistedQuotientIso_projection f s hs hI _ _

/-- Direct image to the base identifies the original quotient with its base line. -/
irreducible_def sectionDivisorQuotientPushforwardIso (m : ℕ) :
    (pushforward f).obj
      (divisorTwistedComplex hI (tensorPower (divisorLineBundle s.ker hI) m)).X₃ ≅
        sectionPoleLine s hI (m + 1) :=
  (pushforward f).mapIso (sectionDivisorQuotientIso f s hs hI m) ≪≫
    (pushforwardComp s f).app _ ≪≫ (pushforwardCongr hs).app _ ≪≫
      (pushforwardId S).app _

end FLT.Mazur.FCurve
