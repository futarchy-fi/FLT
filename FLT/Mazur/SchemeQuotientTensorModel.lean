/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupPullbackComparison
public import FLT.Mazur.FiniteGroupQuotientFlatBaseChange
public import FLT.Mazur.SchemeFiniteGroupQuotient

/-!
# Tensor models of actual affine scheme quotient pullbacks

The tensor spectrum is identified with the pullback of the quotient of an
arbitrary affine scheme. The isomorphism intertwines the actual scheme action
with the tensor action, with the inverse dictated by coordinate contravariance.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FLT.Mazur.SchemeCoordinateAction FLT.Mazur.FiniteGroupQuotient

namespace FLT.Mazur.SchemeQuotientTensor

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} [IsAffine X]
variable (ρ : G →* Aut X)

attribute [local instance] tensorAction

variable (B : Type u) [CommRing B]
variable [Algebra (SchemeFiniteGroupQuotient.invariantCoordinates ρ) B]

/-- The actual tensor model of the base-changed affine scheme. -/
abbrev model : Scheme.{u} := Spec (.of (B ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ]
  Γ(X, ⊤)))

/-- The tensor model maps to the original affine scheme by its canonical affine isomorphism. -/
def toSource : model ρ B ⟶ X :=
  let _ := coordinateAction ρ
  tensorToOriginal G Γ(X, ⊤) B ≫ X.isoSpec.inv

/-- The tensor model projects to the new affine base. -/
def toBase : model ρ B ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap B (B ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤))))

/-- The map from the new base to the actual scheme quotient. -/
def baseMap : Spec (.of B) ⟶ SchemeFiniteGroupQuotient.quotient ρ :=
  let _ := coordinateAction ρ
  tensorBaseMap G Γ(X, ⊤) B

/-- The tensor model is cartesian over the quotient of the original affine scheme. -/
theorem isPullback : IsPullback (toSource ρ B) (toBase ρ B)
    (SchemeFiniteGroupQuotient.quotientMap ρ) (baseMap ρ B) := by
  let _ := coordinateAction ρ
  have h : IsPullback X.isoSpec.inv (FiniteGroupQuotient.quotientMap G Γ(X, ⊤))
      (SchemeFiniteGroupQuotient.quotientMap ρ) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      change X.isoSpec.inv ≫ (X.toSpecΓ ≫ _) = _ ≫ 𝟙 _
      rw [Scheme.isoSpec_inv_toSpecΓ_assoc, Category.comp_id]⟩
  simpa only [toSource, toBase, baseMap, Category.comp_id] using
    (tensorSource_isPullback G Γ(X, ⊤) B).paste_horiz h

/-- The canonical tensor-spectrum comparison with the actual pullback scheme. -/
def iso : model ρ B ≅
    pullback (SchemeFiniteGroupQuotient.quotientMap ρ) (baseMap ρ B) :=
  (isPullback ρ B).isoPullback

/-- The comparison preserves the actual source projection. -/
@[reassoc]
lemma iso_hom_fst : (iso ρ B).hom ≫ pullback.fst _ _ = toSource ρ B :=
  (isPullback ρ B).isoPullback_hom_fst

/-- The comparison preserves the actual base projection. -/
@[reassoc]
lemma iso_hom_snd : (iso ρ B).hom ≫ pullback.snd _ _ = toBase ρ B :=
  (isPullback ρ B).isoPullback_hom_snd

/-- The tensor action projects to the original scheme action with the coordinate inverse. -/
@[reassoc]
lemma toSource_equivariant (g : G) :
    let _ := coordinateAction ρ
    actionMap G (B ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) g ≫
      toSource ρ B = toSource ρ B ≫ (ρ g⁻¹).hom := by
  let _ := coordinateAction ρ
  unfold toSource
  rw [tensorToOriginal_equivariant_assoc]
  rw [Category.assoc]
  congr 1
  rw [← cancel_mono X.toSpecΓ]
  simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
  rw [toSpecΓ_equivariant, Scheme.isoSpec_inv_toSpecΓ_assoc, inv_inv]
  change Spec.map (CommRingCat.ofHom (coordinateHom ρ g)) ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [IsAffine X] in
/-- The tensor action fixes the actual new-base projection. -/
@[reassoc]
lemma toBase_invariant (g : G) :
    let _ := coordinateAction ρ
    actionMap G (B ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) g ≫
      toBase ρ B = toBase ρ B := by
  let _ := coordinateAction ρ
  rw [actionMap, toBase, ← Spec.map_comp]
  apply congrArg Spec.map
  ext b
  exact tensorActionHom_tmul G Γ(X, ⊤) B g b 1 |>.trans (by simp)

/-- Equivariance holds on the actual pullback scheme, including its structure sheaf. -/
@[reassoc]
lemma iso_equivariant (g : G) :
    let _ := coordinateAction ρ
    actionMap G (B ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) g ≫
      (iso ρ B).hom = (iso ρ B).hom ≫
        (FiniteGroupPullback.action ρ _ (SchemeFiniteGroupQuotient.quotientMap_invariant ρ)
          (baseMap ρ B) g⁻¹).hom := by
  let _ := coordinateAction ρ
  exact FiniteGroupPullback.isoPullback_equivariant _ _ _ _ (isPullback ρ B) _ _
    (toSource_equivariant ρ B g) (toBase_invariant ρ B g)

end FLT.Mazur.SchemeQuotientTensor
