/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedGlobalTrivialization

/-!
# Effective descent recovers the original rigidified member classes

The original member recovery isomorphisms preserve the global rigidification.
The resulting global rigidified bundle therefore restricts to the supplied classes.
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


/-- The original recovery preserves the descended global rigidification. -/
theorem rigidifiedFamilyDescendedMember_preserves (i : 𝒰.I₀) :
    (Scheme.Modules.pullback
      (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))).map
        (rigidifiedFamilyDescendedMember f e he T 𝒰 a ha i).hom ≫
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).2.hom =
    (rigidifiedBasePullback f e he (relativeCoverArrow T 𝒰 i)
      (rigidifiedFamilyDescendedBundle f e he T 𝒰 a ha)).2.hom := by
  have h := congrArg (fun m ↦
    (SchemePullbackSquare.squareIso (pointedBaseSection f e he T)
      (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
      (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) (𝒰.f i)
      (pointedBaseSection_naturality f e he (relativeCoverArrow T 𝒰 i))).hom.app
      (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val ≫ m)
    (rigidifiedFamilyGlobalTrivialization_member f e he T 𝒰 a ha i)
  simp only [rigidifiedFamilyBaseTrivialization, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at h
  exact h.symm

/-- The effective recovery is an isomorphism of the original rigidified bundles. -/
def rigidifiedFamilyDescendedRigidifiedIso (i : 𝒰.I₀) :
    RigidifiedIso (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
      (rigidifiedBasePullback f e he (relativeCoverArrow T 𝒰 i)
        (rigidifiedFamilyDescendedBundle f e he T 𝒰 a ha)).2
      (rigidifiedFamilyRepresentative f e he T 𝒰 a i).2 :=
  ⟨rigidifiedFamilyDescendedMember f e he T 𝒰 a ha i,
    rigidifiedFamilyDescendedMember_preserves f e he T 𝒰 a ha i⟩

/-- The global rigidified bundle has each supplied original member class. -/
theorem rigidifiedFamilyDescendedBundle_class (i : 𝒰.I₀) :
    rigidifiedBaseMap f e he (relativeCoverArrow T 𝒰 i)
      (Quotient.mk _ (rigidifiedFamilyDescendedBundle f e he T 𝒰 a ha)) = a i := by
  calc
    _ = Quotient.mk _ (rigidifiedFamilyRepresentative f e he T 𝒰 a i) := by
      apply Quotient.sound
      exact ⟨rigidifiedFamilyDescendedRigidifiedIso f e he T 𝒰 a ha i⟩
    _ = a i := rigidifiedFamilyRepresentative_class f e he T 𝒰 a i

include ha in
/-- Every matching original rigidified family admits a global rigidified class. -/
theorem rigidifiedFamily_exists :
    ∃ b : RigidifiedPic (pointedBaseSection f e he T),
      ∀ i, rigidifiedBaseMap f e he (relativeCoverArrow T 𝒰 i) b = a i :=
  ⟨Quotient.mk _ (rigidifiedFamilyDescendedBundle f e he T 𝒰 a ha),
    rigidifiedFamilyDescendedBundle_class f e he T 𝒰 a ha⟩

end FLT.Mazur.SchemePicard
