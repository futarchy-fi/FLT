/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedFppfPairs
public import FLT.Mazur.ProperFamilyRigidifiedNamedTransitions
public import FLT.Mazur.RelativePicardCoverTriples

/-!
# Original pair transitions restricted to the base triple

Normalize the supplied pair transitions at the three named member coordinates.
Their cocycle follows from uniqueness of preserving rigidified isomorphisms.
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
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)

/-- The original first pair transition normalized on the original triple total space. -/
def rigidifiedFamilyTripleTransition12 (i j k : 𝒰.I₀) :=
  rigidifiedBaseIsoNormalizeNamed f e he (relativeCoverTriple12 T 𝒰 i j k)
    (relativeCoverPairLeft T 𝒰 i j) (relativeCoverPairRight T 𝒰 i j)
    (relativeCoverTripleFirst T 𝒰 i j k) (relativeCoverTripleMiddle T 𝒰 i j k) rfl rfl
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a j)
    (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j)

/-- The original second pair transition uses exactly the same middle coordinate. -/
def rigidifiedFamilyTripleTransition23 (i j k : 𝒰.I₀) :=
  rigidifiedBaseIsoNormalizeNamed f e he (relativeCoverTriple23 T 𝒰 i j k)
    (relativeCoverPairLeft T 𝒰 j k) (relativeCoverPairRight T 𝒰 j k)
    (relativeCoverTripleMiddle T 𝒰 i j k) (relativeCoverTripleLast T 𝒰 i j k)
    (relativeCoverTriple23_left T 𝒰 i j k) rfl
    (rigidifiedFamilyRepresentative f e he T 𝒰 a j)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a k)
    (rigidifiedFamilyPairTransition f e he T 𝒰 a ha j k)

/-- The original outer pair transition normalized at the first and last coordinates. -/
def rigidifiedFamilyTripleTransition13 (i j k : 𝒰.I₀) :=
  rigidifiedBaseIsoNormalizeNamed f e he (relativeCoverTriple13 T 𝒰 i j k)
    (relativeCoverPairLeft T 𝒰 i k) (relativeCoverPairRight T 𝒰 i k)
    (relativeCoverTripleFirst T 𝒰 i j k) (relativeCoverTripleLast T 𝒰 i j k)
    (relativeCoverTriple13_left T 𝒰 i j k) (relativeCoverTriple13_right T 𝒰 i j k)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a i)
    (rigidifiedFamilyRepresentative f e he T 𝒰 a k)
    (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i k)

/-- The original normalized transitions satisfy the cocycle on the original base triple. -/
theorem rigidifiedFamilyTripleTransition_cocycle (i j k : 𝒰.I₀) :
    (rigidifiedFamilyTripleTransition12 f e he T 𝒰 a ha i j k).val ≪≫
        (rigidifiedFamilyTripleTransition23 f e he T 𝒰 a ha i j k).val =
      (rigidifiedFamilyTripleTransition13 f e he T 𝒰 a ha i j k).val := by
  exact congrArg Subtype.val
    ((pointedFamily_rigidifiedIso_subsingleton f e he (relativeCoverTriple T 𝒰 i j k)
      _ _).elim
      (rigidifiedIsoTrans (rigidifiedFamilyTripleTransition12 f e he T 𝒰 a ha i j k)
        (rigidifiedFamilyTripleTransition23 f e he T 𝒰 a ha i j k))
      (rigidifiedFamilyTripleTransition13 f e he T 𝒰 a ha i j k))

end FLT.Mazur.SchemePicard
