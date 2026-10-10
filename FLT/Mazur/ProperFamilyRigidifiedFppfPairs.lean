/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedTransitions
public import FLT.Mazur.RelativePicardFppfPairs
public import FLT.Mazur.SchemeIndependentPairNormalization

/-!
# Actual pair isomorphisms from matching rigidified fppf classes

Choose genuine representatives of the supplied member classes. Their matching
condition produces unique rigidified comparisons on base-pair total spaces.
The original pair-overlap charts transport those comparisons to the actual
unequal overlaps of the total-space fppf cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))

/-- Choose an actual bundle and original trivialization for each supplied member class. -/
def rigidifiedFamilyRepresentative (i : 𝒰.I₀) :
    RigidifiedBundle (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)) :=
  Quotient.out (a i)

/-- The representative has exactly the supplied rigidified isomorphism class. -/
theorem rigidifiedFamilyRepresentative_class (i : 𝒰.I₀) :
    Quotient.mk _ (rigidifiedFamilyRepresentative f e he T 𝒰 a i) = a i :=
  Quotient.out_eq (a i)

/-- Matching is imposed only on the supplied classes along original base-pair projections. -/
def RigidifiedFamilyMatching : Prop := ∀ i j,
  rigidifiedBaseMap f e he (relativeCoverPairLeft T 𝒰 i j) (a i) =
    rigidifiedBaseMap f e he (relativeCoverPairRight T 𝒰 i j) (a j)

/-- Class matching yields equality of the original restricted Picard representatives. -/
theorem rigidifiedFamilyRepresentative_matching
    (ha : RigidifiedFamilyMatching f e he T 𝒰 a) (i j : 𝒰.I₀) :
    rigidifiedBaseClass f e he (relativeCoverPairLeft T 𝒰 i j)
        (rigidifiedFamilyRepresentative f e he T 𝒰 a i) =
      rigidifiedBaseClass f e he (relativeCoverPairRight T 𝒰 i j)
        (rigidifiedFamilyRepresentative f e he T 𝒰 a j) := by
  have h := ha i j
  rw [← rigidifiedFamilyRepresentative_class f e he T 𝒰 a i,
    ← rigidifiedFamilyRepresentative_class f e he T 𝒰 a j] at h
  exact congrArg (fun c ↦ (rigidifiedKernel
    (pointedBaseSection f e he (relativeCoverPair T 𝒰 i j)) c).val) h

variable [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)

/-- The original rigidified pair comparison is constructed from class matching. -/
def rigidifiedFamilyPairTransition (i j : 𝒰.I₀) :=
  rigidifiedTransition f e he (relativeCoverPairLeft T 𝒰 i j)
    (relativeCoverPairRight T 𝒰 i j)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a j)
    (rigidifiedFamilyRepresentative_matching f e he T 𝒰 a ha i j)

/-- Transport the original transition to the actual pair overlap of the total-space cover. -/
def rigidifiedFamilyPairIso (i j : 𝒰.I₀) :
    (Scheme.Modules.pullback
      (Limits.pullback.fst ((relativeTotalCover f T 𝒰).f i)
        ((relativeTotalCover f T 𝒰).f j))).obj
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val ≅
    (Scheme.Modules.pullback
      (Limits.pullback.snd ((relativeTotalCover f T 𝒰).f i)
        ((relativeTotalCover f T 𝒰).f j))).obj
      (rigidifiedFamilyRepresentative f e he T 𝒰 a j).1.val :=
  SchemeIndependentPairNormalization.normalize
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
    (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
    (relativeCoverPairTotalIso f T 𝒰 i j).inv _ _
    (relativeCoverPairTotalIso_inv_fst f T 𝒰 i j)
    (relativeCoverPairTotalIso_inv_snd f T 𝒰 i j) _ _
    (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j).val

end FLT.Mazur.SchemePicard
