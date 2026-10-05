/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.ClosedIdealQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Images of morphisms of local proartinian coefficient rings

The quotient by the closed kernel is a local proartinian object with the
original residue field. It embeds in the target and is the actual image.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace Deformation.ProartinianCat

universe u
variable {O : Type u} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {U A : ProartinianCat O} (f : U ⟶ A)

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- The kernel of a parameter morphism is closed. -/
theorem imageKernel_closed : IsClosed (RingHom.ker f.hom.toRingHom : Set U) :=
  isClosed_singleton.preimage f.hom.cont

/-- Quotient presentation of the actual image, retaining the original residue coefficients. -/
def imageObject : ProartinianCat O :=
  closedIdealQuotient U (RingHom.ker f.hom.toRingHom)
    (imageKernel_closed f) (RingHom.ker_ne_top _)

/-- The surjection to the image object. -/
def imageProjection : U ⟶ imageObject f :=
  closedIdealQuotientHom U (RingHom.ker f.hom.toRingHom)
    (imageKernel_closed f) (RingHom.ker_ne_top _)

/-- Every image coefficient has a preimage in the source. -/
theorem imageProjection_surjective : Function.Surjective (imageProjection f).hom :=
  Ideal.Quotient.mk_surjective

/-- The induced injection of the image object into the given target. -/
def imageInclusion : imageObject f ⟶ A where
  hom :=
    { toAlgHom := Ideal.kerLiftAlg f.hom.toAlgHom
      cont := (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap.continuous_iff.mpr
        f.hom.cont }

/-- The image inclusion is injective. -/
theorem imageInclusion_injective : Function.Injective (imageInclusion f).hom :=
  Ideal.kerLiftAlg_injective _

/-- The original map factors through its image with its original coefficient maps. -/
@[simp] theorem imageProjection_inclusion : imageProjection f ≫ imageInclusion f = f := by
  apply hom_ext
  ext x
  rfl

/-- Algebraic identification with the subalgebra image in the target. -/
def imageEquivRange : imageObject f ≃ₐ[O] f.hom.toAlgHom.range :=
  Ideal.quotientKerEquivRange f.hom.toAlgHom

/-- The image inclusion has exactly the same range as the original morphism. -/
theorem imageInclusion_range :
    (imageInclusion f).hom.toAlgHom.range = f.hom.toAlgHom.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := imageProjection_surjective f y
    exact ⟨z, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(imageProjection f).hom y, rfl⟩

/-- The image inclusion commutes with the canonical map to the original residue field. -/
@[simp] theorem imageInclusion_residue :
    imageInclusion f ≫ toResidueField A = toResidueField (imageObject f) :=
  Subsingleton.elim _ _

/-- Noetherianity descends from the source to its image, without a subring assertion. -/
theorem imageObject_isNoetherian [IsNoetherianRing U] : IsNoetherianRing (imageObject f) :=
  isNoetherianRing_of_surjective U (imageObject f) (imageProjection f).hom.toRingHom
    (imageProjection_surjective f)

end Deformation.ProartinianCat
