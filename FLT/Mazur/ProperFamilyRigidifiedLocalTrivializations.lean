/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedLineDescent

/-!
# Local trivializations of the effectively descended line

The actual member recoveries transfer each original rigidification to the
restricted global line. The section square supplies local trivializations of
its section pullback on the base cover; their effective gluing remains separate.
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

/-- Transfer the original member rigidification to the restricted effective global line. -/
def rigidifiedFamilyRestrictedBundle (i : 𝒰.I₀) :
    RigidifiedBundle (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)) :=
  ⟨⟨(Scheme.Modules.pullback ((relativeTotalCover f T 𝒰).f i)).obj
      (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val,
    (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).property.pullback _⟩,
    (Scheme.Modules.pullback (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))).mapIso
      (rigidifiedFamilyDescendedMember f e he T 𝒰 a ha i) ≪≫
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).2⟩

/-- The original recovery preserves the transferred rigidification by construction. -/
def rigidifiedFamilyRestrictedIso (i : 𝒰.I₀) :
    RigidifiedIso (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
      (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha i).2
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).2 :=
  ⟨rigidifiedFamilyDescendedMember f e he T 𝒰 a ha i, rfl⟩

/-- Each transferred member has exactly the supplied original rigidified class. -/
theorem rigidifiedFamilyRestrictedBundle_class (i : 𝒰.I₀) :
    Quotient.mk _ (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha i) = a i := by
  calc
    _ = Quotient.mk _ (rigidifiedFamilyRepresentative f e he T 𝒰 a i) :=
      by
        apply Quotient.sound
        exact ⟨rigidifiedFamilyRestrictedIso f e he T 𝒰 a ha i⟩
    _ = a i := rigidifiedFamilyRepresentative_class f e he T 𝒰 a i

/-- The specified trivializations give actual local frames on the original base cover. -/
def rigidifiedFamilyBaseTrivialization (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (𝒰.f i)).obj
      ((Scheme.Modules.pullback (pointedBaseSection f e he T)).obj
        (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val) ≅ structureModule (𝒰.X i) :=
  ((SchemePullbackSquare.squareIso (pointedBaseSection f e he T)
    (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
    (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) (𝒰.f i)
    (pointedBaseSection_naturality f e he (relativeCoverArrow T 𝒰 i))).app
      (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val).symm ≪≫
    (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha i).2

end FLT.Mazur.SchemePicard
