/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFamilyIdentityComparison
public import FLT.Mazur.ProperFamilyIteratedSectionOrbits

/-!
# The prescribed identity on original family sections

The original twisting-line comparison is exactly the sheaf pullback identity.
This identifies the representative-level unit, including its actual section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ProperFamilyTests LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {f : X ⟶ S} [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {A : Family f}

/-- The prescribed base-line identity carries the directly pulled original section. -/
lemma familySectionMap_id_section
    (s : RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst)) :
    (ModuleSheafTensor.map (𝟙 ((pullback A.fst).obj L))
      ((pullback A.snd).map ((pullbackId A.base).hom.app s.val.baseLine.val))).app ⊤
      (familySectionMap L hL hV (𝟙 A) s).val.section_ = s.val.section_ :=
  originalFamilyPullSection_id A.fst A.snd L s.val.baseLine s.val.section_

/-- Every section-preserving original unit is the prescribed pullback identity. -/
lemma familySectionMap_id_iso_unique
    (s : RelativeSection A.snd ((pullback A.fst).obj L) (hL.pullback A.fst))
    (e : (familySectionMap L hL hV (𝟙 A) s).val.baseLine.val ≅ s.val.baseLine.val)
    (he : (ModuleSheafTensor.map (𝟙 ((pullback A.fst).obj L))
      ((pullback A.snd).map e.hom)).app ⊤
      (familySectionMap L hL hV (𝟙 A) s).val.section_ = s.val.section_) :
    e = (pullbackId A.base).app s.val.baseLine.val :=
  familyOriginalTwistIso_unique L hL hV _ s e _ he
    (familySectionMap_id_section L hL hV s)

end FLT.Mazur.CartierAbel
