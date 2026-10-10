/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedTripleTransitions
public import FLT.Mazur.RelativePicardTripleCoordinates
public import FLT.Mazur.SchemeIndependentNormalizationSquare
public import FLT.Mazur.SchemeIndependentTripleCocycle

/-!
# Original total-cover edges and rigidified triple transport

Each original unequal edge is the prescribed normalization of the base-triple
transition through the inverse total-space chart, at shared coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SchemeIndependentPairNormalization
open SchemeFamilyTripleOverlap SchemeIndependentTripleCocycle
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)

/-- Transport the original base-triple edge 12 through the exact inverse chart. -/
def rigidifiedFamilyTripleTransport12 (i j k : 𝒰.I₀) :=
  SchemeIndependentPairNormalization.normalize
    (relativeTotalMap f (relativeCoverTripleFirst T 𝒰 i j k))
    (relativeTotalMap f (relativeCoverTripleMiddle T 𝒰 i j k))
    (relativeCoverTripleTotalIso f T 𝒰 i j k).inv
    (coord1 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k))
    (coord2 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k))
    (relativeCoverTripleTotalIso_inv_coord1 f T 𝒰 i j k)
    (relativeCoverTripleTotalIso_inv_coord2 f T 𝒰 i j k)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
    (rigidifiedFamilyRepresentative f e he T 𝒰 a j).1.val
    (rigidifiedFamilyTripleTransition12 f e he T 𝒰 a ha i j k).val

/-- The actual total-cover edge 12 is exactly the transported original transition. -/
theorem rigidifiedFamilyTripleEdge12_eq (i j k : 𝒰.I₀) :
    edge12 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k)
        (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
        (rigidifiedFamilyRepresentative f e he T 𝒰 a j).1.val
        (rigidifiedFamilyPairIso f e he T 𝒰 a ha i j) =
      rigidifiedFamilyTripleTransport12 f e he T 𝒰 a ha i j k := by
  dsimp only [edge12, rigidifiedFamilyPairIso, rigidifiedFamilyTripleTransport12,
    rigidifiedFamilyTripleTransition12]
  rw [rigidifiedBaseIsoNormalizeNamed_val]
  apply normalize_square
  exact relativeCoverTripleTotalIso_inv_pair12 f T 𝒰 i j k

/-- Transport the original base-triple edge 23 through the exact inverse chart. -/
def rigidifiedFamilyTripleTransport23 (i j k : 𝒰.I₀) :=
  SchemeIndependentPairNormalization.normalize
    (relativeTotalMap f (relativeCoverTripleMiddle T 𝒰 i j k))
    (relativeTotalMap f (relativeCoverTripleLast T 𝒰 i j k))
    (relativeCoverTripleTotalIso f T 𝒰 i j k).inv
    (coord2 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k))
    (coord3 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k))
    (relativeCoverTripleTotalIso_inv_coord2 f T 𝒰 i j k)
    (relativeCoverTripleTotalIso_inv_coord3 f T 𝒰 i j k)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a j).1.val
    (rigidifiedFamilyRepresentative f e he T 𝒰 a k).1.val
    (rigidifiedFamilyTripleTransition23 f e he T 𝒰 a ha i j k).val

/-- The actual total-cover edge 23 is exactly the transported original transition. -/
theorem rigidifiedFamilyTripleEdge23_eq (i j k : 𝒰.I₀) :
    edge23 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k)
        (rigidifiedFamilyRepresentative f e he T 𝒰 a j).1.val
        (rigidifiedFamilyRepresentative f e he T 𝒰 a k).1.val
        (rigidifiedFamilyPairIso f e he T 𝒰 a ha j k) =
      rigidifiedFamilyTripleTransport23 f e he T 𝒰 a ha i j k := by
  dsimp only [edge23, rigidifiedFamilyPairIso, rigidifiedFamilyTripleTransport23,
    rigidifiedFamilyTripleTransition23]
  rw [rigidifiedBaseIsoNormalizeNamed_val]
  apply normalize_square
  exact relativeCoverTripleTotalIso_inv_pair23 f T 𝒰 i j k

/-- Transport the original base-triple edge 13 through the exact inverse chart. -/
def rigidifiedFamilyTripleTransport13 (i j k : 𝒰.I₀) :=
  SchemeIndependentPairNormalization.normalize
    (relativeTotalMap f (relativeCoverTripleFirst T 𝒰 i j k))
    (relativeTotalMap f (relativeCoverTripleLast T 𝒰 i j k))
    (relativeCoverTripleTotalIso f T 𝒰 i j k).inv
    (coord1 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k))
    (coord3 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      ((relativeTotalCover f T 𝒰).f k))
    (relativeCoverTripleTotalIso_inv_coord1 f T 𝒰 i j k)
    (relativeCoverTripleTotalIso_inv_coord3 f T 𝒰 i j k)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
    (rigidifiedFamilyRepresentative f e he T 𝒰 a k).1.val
    (rigidifiedFamilyTripleTransition13 f e he T 𝒰 a ha i j k).val

/-- The actual total-cover edge 13 is exactly the transported original transition. -/
theorem rigidifiedFamilyTripleEdge13_eq (i j k : 𝒰.I₀) :
    edge13 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k)
        (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val
        (rigidifiedFamilyRepresentative f e he T 𝒰 a k).1.val
        (rigidifiedFamilyPairIso f e he T 𝒰 a ha i k) =
      rigidifiedFamilyTripleTransport13 f e he T 𝒰 a ha i j k := by
  dsimp only [edge13, rigidifiedFamilyPairIso, rigidifiedFamilyTripleTransport13,
    rigidifiedFamilyTripleTransition13]
  rw [rigidifiedBaseIsoNormalizeNamed_val]
  apply normalize_square
  exact relativeCoverTripleTotalIso_inv_pair13 f T 𝒰 i j k

end FLT.Mazur.SchemePicard
