/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityKernelPair
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# The internal equivalence relation of the constructed original source

Reflexivity, symmetry, and composition are constructed as actual scheme maps
from equality of the original Picard classes. No quotient scheme is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityOriginalRelation
open HilbertChart CartierAbel FCurve SchemePicard OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

local notation "U" => OrderedHilbertIdentityOriginalSection.sourceTest f hB
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hB

/-- The unique actual relation map of two equal-class source morphisms. -/
def relationLift {T : Over (Spec (.of R))}
    (a b : T ⟶ U)
    (h : (relativeFppfSheaf f).obj.map a.op (sU) =
      (relativeFppfSheaf f).obj.map b.op (sU)) :
    T ⟶ relation f hB :=
  (lift f hB a b h).choose

/-- The first projection of the constructed relation map. -/
theorem relationLift_fst {T : Over (Spec (.of R))}
    (a b : T ⟶ U) (h) :
    relationLift f hB a b h ≫ fst f hB = a :=
  (lift f hB a b h).choose_spec.1.1

/-- The second projection of the constructed relation map. -/
theorem relationLift_snd {T : Over (Spec (.of R))}
    (a b : T ⟶ U) (h) :
    relationLift f hB a b h ≫ snd f hB = b :=
  (lift f hB a b h).choose_spec.1.2

/-- The diagonal relation morphism is constructed from equality with itself. -/
def relationRefl : U ⟶ relation f hB :=
  relationLift f hB (𝟙 _) (𝟙 _) rfl

/-- The inverse relation morphism exchanges the actual projections. -/
def relationSwap : relation f hB ⟶ relation f hB :=
  relationLift f hB (snd f hB)
    (fst f hB) (equal_class f hB).symm

/-- Equality of original classes is transitive on the actual composable-pair scheme. -/
theorem composable_class :
    (relativeFppfSheaf f).obj.map
      (pullback.fst (snd f hB) (fst f hB) ≫
        fst f hB).op (sU) =
    (relativeFppfSheaf f).obj.map
      (pullback.snd (snd f hB) (fst f hB) ≫
        snd f hB).op (sU) := by
  calc
    _ = (relativeFppfSheaf f).obj.map
        (pullback.fst (snd f hB) (fst f hB) ≫
          snd f hB).op (sU) := by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [equal_class]
    _ = (relativeFppfSheaf f).obj.map
        (pullback.snd (snd f hB) (fst f hB) ≫
          fst f hB).op (sU) := by
      rw [pullback.condition]
    _ = _ := by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rw [equal_class]

/-- Composition is an actual scheme morphism from the composable-pair pullback. -/
def relationComp :
    Limits.pullback (snd f hB) (fst f hB) ⟶
      relation f hB :=
  relationLift f hB (pullback.fst _ _ ≫ fst f hB)
    (pullback.snd _ _ ≫ snd f hB)
    (composable_class f hB)

/-- The represented original equal-class relation is an internal equivalence relation. -/
def equivalenceRelation :
    CategoryTheory.EquivalenceRelation
      (fst f hB) (snd f hB) where
  right_cancellation _ _ _ h₁ h₂ := hom_ext f hB h₁ h₂
  r := relationRefl f hB
  reflexivity₁ := relationLift_fst f hB _ _ _
  reflexivity₂ := relationLift_snd f hB _ _ _
  s := relationSwap f hB
  symmetry₁ := relationLift_fst f hB _ _ _
  symmetry₂ := relationLift_snd f hB _ _ _
  c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  isLimit := pullbackIsPullback _ _
  t := relationComp f hB
  transitivity₁ := relationLift_fst f hB _ _ _
  transitivity₂ := relationLift_snd f hB _ _ _

/-- Swapping twice is the identity as an actual scheme morphism. -/
theorem relationSwap_involutive :
    relationSwap f hB ≫ relationSwap f hB = 𝟙 _ := by
  have h₁ : relationSwap f hB ≫ fst f hB =
      snd f hB := (equivalenceRelation f hB).symmetry₁
  have h₂ : relationSwap f hB ≫ snd f hB =
      fst f hB := (equivalenceRelation f hB).symmetry₂
  apply hom_ext f hB
  · rw [Category.assoc, h₁, h₂, Category.id_comp]
  · rw [Category.assoc, h₂, h₁, Category.id_comp]

/-- Swapping the full original relation is an actual relative scheme isomorphism. -/
def swapIso : relation f hB ≅ relation f hB where
  hom := relationSwap f hB
  inv := relationSwap f hB
  hom_inv_id := relationSwap_involutive f hB
  inv_hom_id := relationSwap_involutive f hB

/-- Both full relation endpoints are etale over the original source. -/
instance fst_etale : Etale (fst f hB).left := by
  let e := (Over.forget _).mapIso (swapIso f hB)
  have he : e.hom ≫ (snd f hB).left = (fst f hB).left :=
    congrArg Over.Hom.left (equivalenceRelation f hB).symmetry₂
  rw [← he]
  infer_instance

/-- Reflexivity is open in the full relation, without discarding its other arrows. -/
instance refl_isOpenImmersion : IsOpenImmersion (relationRefl f hB).left :=
  UnramifiedSectionImmersion.isOpenImmersion (snd f hB).left (relationRefl f hB).left
    (congrArg Over.Hom.left (equivalenceRelation f hB).reflexivity₂)

end FLT.Mazur.OrderedHilbertIdentityOriginalRelation
