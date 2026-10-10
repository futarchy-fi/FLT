/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedTripleEdges

/-!
# Original unequal triple cocycles for rigidified fppf pairs

Transport the proved base-triple law through its actual total-space chart.
The three original total-cover edges use the same middle coordinate, so the
transported law is exactly the required original unequal triple cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SchemeIndependentPairNormalization
open SchemeIndependentTripleCocycle
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)

/-- The transported triple transitions retain the cocycle through the original chart. -/
theorem rigidifiedFamilyTripleTransport_cocycle (i j k : 𝒰.I₀) :
    rigidifiedFamilyTripleTransport12 f e he T 𝒰 a ha i j k ≪≫
        rigidifiedFamilyTripleTransport23 f e he T 𝒰 a ha i j k =
      rigidifiedFamilyTripleTransport13 f e he T 𝒰 a ha i j k := by
  dsimp only [rigidifiedFamilyTripleTransport12, rigidifiedFamilyTripleTransport23,
    rigidifiedFamilyTripleTransport13]
  rw [← normalize_trans]
  rw [rigidifiedFamilyTripleTransition_cocycle]

/-- The original pair isomorphisms satisfy the original unequal total-cover cocycle. -/
theorem rigidifiedFamilyPairIso_cocycle (i j k : 𝒰.I₀) :
    Cocycle ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k)
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
      (rigidifiedFamilyRepresentative f e he T 𝒰 a j).1.val
      (rigidifiedFamilyRepresentative f e he T 𝒰 a k).1.val
      (rigidifiedFamilyPairIso f e he T 𝒰 a ha i j)
      (rigidifiedFamilyPairIso f e he T 𝒰 a ha j k)
      (rigidifiedFamilyPairIso f e he T 𝒰 a ha i k) := by
  unfold Cocycle
  rw [rigidifiedFamilyTripleEdge12_eq, rigidifiedFamilyTripleEdge23_eq,
    rigidifiedFamilyTripleEdge13_eq]
  exact congrArg Iso.hom (rigidifiedFamilyTripleTransport_cocycle f e he T 𝒰 a ha i j k)

end FLT.Mazur.SchemePicard
