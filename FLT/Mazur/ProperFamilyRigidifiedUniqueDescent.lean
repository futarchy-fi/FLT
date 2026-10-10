/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedComparisonGluing
public import FLT.Mazur.ProperFamilyRigidifiedEffectiveDescent

/-!
# Unique effective descent for rigidified classes

Equality on an original fppf cover supplies local rigidified comparisons.
Their global underlying isomorphism identifies the global rigidified classes.
Together with effective descent this gives a unique matching-family amalgamation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)

/-- Rigidified classes are determined by their restrictions to an original fppf family. -/
theorem rigidifiedFamily_ext (a b : RigidifiedPic (pointedBaseSection f e he T))
    (h : ∀ i, rigidifiedBaseMap f e he (relativeCoverArrow T 𝒰 i) a =
      rigidifiedBaseMap f e he (relativeCoverArrow T 𝒰 i) b) : a = b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro L M h
  have hi (i : 𝒰.I₀) : Nonempty
      (RigidifiedIso (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
        (rigidifiedBasePullback f e he (relativeCoverArrow T 𝒰 i) L).2
        (rigidifiedBasePullback f e he (relativeCoverArrow T 𝒰 i) M).2) :=
    Quotient.exact (h i)
  apply Quotient.sound
  apply (rigidifiedIso_nonempty_iff (Limits.pullback.snd f T.hom)
    (pointedBaseSection f e he T) (pointedBaseSection_snd f e he T)
    L.1.property L.2 M.2).mpr
  exact ⟨rigidifiedFamilyComparisonIso f e he T 𝒰 L M (fun i ↦ (hi i).some)⟩

/-- Every matching original rigidified family has a unique global amalgamation. -/
theorem rigidifiedFamily_existsUnique
    (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
    (ha : RigidifiedFamilyMatching f e he T 𝒰 a) :
    ∃! b : RigidifiedPic (pointedBaseSection f e he T),
      ∀ i, rigidifiedBaseMap f e he (relativeCoverArrow T 𝒰 i) b = a i := by
  obtain ⟨b, hb⟩ := rigidifiedFamily_exists f e he T 𝒰 a ha
  refine ⟨b, hb, fun c hc ↦ rigidifiedFamily_ext f e he T 𝒰 c b ?_⟩
  exact fun i ↦ (hc i).trans (hb i).symm

/-- The rigidified presheaf satisfies the sheaf condition on every original fppf family. -/
theorem rigidifiedFamily_isSheafFor :
    Presieve.IsSheafFor (rigidifiedPresheaf f e he)
      (Presieve.ofArrows (relativeCoverMember T 𝒰) (relativeCoverArrow T 𝒰)) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro a ha
  apply rigidifiedFamily_existsUnique f e he T 𝒰 a
  exact fun i j ↦ ha i j (relativeCoverPair T 𝒰 i j)
    (relativeCoverPairLeft T 𝒰 i j) (relativeCoverPairRight T 𝒰 i j)
    (relativeCoverPair_condition T 𝒰 i j)

end FLT.Mazur.SchemePicard
