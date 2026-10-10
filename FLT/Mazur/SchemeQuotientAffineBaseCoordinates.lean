/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeQuotientTensorModel
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Coordinates for arbitrary affine base changes of scheme quotients

An actual morphism from an affine scheme to the invariant spectrum supplies
the required algebra structure on its global sections. Geometric flatness
implies module flatness for exactly this algebra, so the tensor fixed-ring
comparison applies without asking for a chosen ring presentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.SchemeQuotientAffineBase

universe u
variable {G : Type u} [Group G] {X S : Scheme.{u}} [IsAffine S]
variable (ρ : G →* Aut X) (f : S ⟶ quotient ρ)

/-- The actual coordinate map of an arbitrary affine base morphism. -/
def coordinateMap : invariantCoordinates ρ →+* Γ(S, ⊤) :=
  (Spec.preimage (S.isoSpec.inv ≫ f)).hom

/-- The algebra structure is induced by the actual morphism on the new base. -/
@[instance_reducible]
def coordinateAlgebra : Algebra (invariantCoordinates ρ) Γ(S, ⊤) :=
  (coordinateMap ρ f).toAlgebra

/-- The constructed coordinate map recovers the original scheme morphism. -/
@[reassoc]
lemma coordinateMap_spec :
    Spec.map (CommRingCat.ofHom (coordinateMap ρ f)) = S.isoSpec.inv ≫ f :=
  Spec.map_preimage _

/-- The actual scalar map of the constructed algebra is the coordinate pullback. -/
lemma coordinateAlgebra_map :
    let _ := coordinateAlgebra ρ f
    algebraMap (invariantCoordinates ρ) Γ(S, ⊤) = coordinateMap ρ f := rfl

/-- Geometric flatness gives flatness over the actual invariant coordinate ring. -/
theorem coordinate_flat [Flat f] :
    let _ := coordinateAlgebra ρ f
    Module.Flat (invariantCoordinates ρ) Γ(S, ⊤) := by
  have h : Flat (Spec.map (CommRingCat.ofHom (coordinateMap ρ f))) := by
    rw [coordinateMap_spec]
    infer_instance
  exact Flat.SpecMap_iff.mp h

/-- The tensor construction uses precisely the actual affine base morphism. -/
lemma tensor_baseMap :
    let _ := coordinateAlgebra ρ f
    SchemeQuotientTensor.baseMap ρ Γ(S, ⊤) = S.isoSpec.inv ≫ f :=
  coordinateMap_spec ρ f

variable [IsAffine X]

/-- The tensor spectrum associated to an arbitrary affine base morphism. -/
abbrev model : Scheme.{u} :=
  let _ := coordinateAlgebra ρ f
  SchemeQuotientTensor.model ρ Γ(S, ⊤)

/-- The tensor model projects to the actual original affine scheme. -/
def toSource : model ρ f ⟶ X :=
  let _ := coordinateAlgebra ρ f
  SchemeQuotientTensor.toSource ρ Γ(S, ⊤)

/-- The tensor model projects to the actual affine new base. -/
def toBase : model ρ f ⟶ S :=
  let _ := coordinateAlgebra ρ f
  SchemeQuotientTensor.toBase ρ Γ(S, ⊤) ≫ S.isoSpec.inv

/-- The constructed tensor model is cartesian over the actual affine base morphism. -/
theorem isPullback : CategoryTheory.IsPullback (toSource ρ f) (toBase ρ f)
    (quotientMap ρ) f := by
  let _ := coordinateAlgebra ρ f
  have h : CategoryTheory.IsPullback (SchemeQuotientTensor.baseMap ρ Γ(S, ⊤))
      S.isoSpec.inv (𝟙 _) f :=
    CategoryTheory.IsPullback.of_vert_isIso ⟨by rw [tensor_baseMap, Category.comp_id]⟩
  simpa only [Category.comp_id, toSource, toBase] using
    (SchemeQuotientTensor.isPullback ρ Γ(S, ⊤)).paste_vert h

/-- The actual tensor-spectrum identification for any affine base morphism. -/
def iso : model ρ f ≅ Limits.pullback (quotientMap ρ) f := (isPullback ρ f).isoPullback

/-- The affine model identification preserves the source projection. -/
@[reassoc]
lemma iso_hom_fst : (iso ρ f).hom ≫ Limits.pullback.fst _ _ = toSource ρ f :=
  (isPullback ρ f).isoPullback_hom_fst

/-- The affine model identification preserves the base projection. -/
@[reassoc]
lemma iso_hom_snd : (iso ρ f).hom ≫ Limits.pullback.snd _ _ = toBase ρ f :=
  (isPullback ρ f).isoPullback_hom_snd

end FLT.Mazur.SchemeQuotientAffineBase
