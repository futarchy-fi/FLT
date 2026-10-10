/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedBaseFramePairs
public import FLT.Mazur.SchemeIndependentFrameGluing

/-!
# Global rigidification of the effectively descended family line

The original compatible base frames descend to a global section trivialization.
Its restriction retains each specified original frame on the base cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)


/-- Descend the specified original base frames to a global section trivialization. -/
def rigidifiedFamilyGlobalTrivialization :
    (Scheme.Modules.pullback (pointedBaseSection f e he T)).obj
      (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val ≅ structureModule T.left :=
  SchemeFppfFamily.IndependentLineData.glueFrame 𝒰
    ((lineBundlePullback (pointedBaseSection f e he T)).obj
      (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha))
    (rigidifiedFamilyBaseTrivialization f e he T 𝒰 a ha)
    (rigidifiedFamilyBaseTrivialization_pair f e he T 𝒰 a ha)

/-- The global trivialization recovers the exact original frame on every base member. -/
theorem rigidifiedFamilyGlobalTrivialization_member (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (𝒰.f i)).map
        (rigidifiedFamilyGlobalTrivialization f e he T 𝒰 a ha).hom ≫
      (modulePullbackUnitIso (𝒰.f i)).hom =
        (rigidifiedFamilyBaseTrivialization f e he T 𝒰 a ha i).hom :=
  SchemeFppfFamily.IndependentLineData.glueFrame_member 𝒰
    ((lineBundlePullback (pointedBaseSection f e he T)).obj
      (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha))
    (rigidifiedFamilyBaseTrivialization f e he T 𝒰 a ha)
    (rigidifiedFamilyBaseTrivialization_pair f e he T 𝒰 a ha) i

/-- The effective global line now carries its descended actual rigidification. -/
def rigidifiedFamilyDescendedBundle : RigidifiedBundle (pointedBaseSection f e he T) :=
  ⟨rigidifiedFamilyDescendedLine f e he T 𝒰 a ha,
    rigidifiedFamilyGlobalTrivialization f e he T 𝒰 a ha⟩

end FLT.Mazur.SchemePicard
