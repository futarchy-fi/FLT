/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedFppfCocycles
public import FLT.Mazur.ProperFamilyRigidifiedFppfDiagonals
public import FLT.Mazur.SchemeIndependentFamilyLineData

/-!
# Effective line descent from matching rigidified classes

The original representatives, pair isomorphisms and proved overlap laws
construct independent line descent data. Effectiveness constructs a line
bundle and its original member recoveries; global rigidification is separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity SchemeFppfFamily
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)

/-- Matching classes give effective independent line data on the original total cover. -/
def rigidifiedFamilyIndependentLineData : IndependentLineData (relativeTotalCover f T 𝒰) where
  obj i := (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1
  overlap ij := rigidifiedFamilyPairIso f e he T 𝒰 a ha ij.1 ij.2
  diagonal := rigidifiedFamilyPairIso_diagonal f e he T 𝒰 a ha
  cocycle ijk := rigidifiedFamilyPairIso_cocycle f e he T 𝒰 a ha ijk.1.1 ijk.1.2 ijk.2

/-- Effectiveness constructs the underlying global line bundle from the supplied classes. -/
def rigidifiedFamilyDescendedLine : LineBundleCat (Limits.pullback f T.hom) :=
  (rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).descended

/-- The descended line recovers each original representative on its exact total-space member. -/
def rigidifiedFamilyDescendedMember (i : 𝒰.I₀) :
    (Scheme.Modules.pullback ((relativeTotalCover f T 𝒰).f i)).obj
        (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val ≅
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).1.val :=
  (rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).descendedMemberRecovery i

end FLT.Mazur.SchemePicard
