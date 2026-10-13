/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityOriginalRelation

/-!
# Uniqueness and existence for the entire original relation

Pull back every first component along an arbitrary source map. On these
actual open subschemes the original mixed-intersection property gives unique
lifts. Gluing produces a morphism on the whole test, including maps meeting
many components in either endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityOriginalRelation
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "A" => OrderedHilbertIdentityOriginalSection.test f hL
local notation "k" => OrderedHilbertIdentityOriginalSection.parameter f hL
local notation "U" => OrderedHilbertIdentityOriginalSection.sourceTest f hL
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL
local notation "sA" => OrderedHilbertIdentityOriginalSection.sectionAt f hL
local notation "ι" => OrderedHilbertIdentityOriginalSection.component f hL

/-- The two original endpoints distinguish arbitrary maps into the relation scheme. -/
theorem hom_ext {W : Over (Spec (.of R))} {a b : W ⟶ relation f hL}
    (h₁ : a ≫ fst f hL = b ≫ fst f hL)
    (h₂ : a ≫ snd f hL = b ≫ snd f hL) : a = b := by
  let t := a ≫ fst f hL
  apply relativeCoproductPull_hom_ext A t
  intro x
  let v := relativeCoproductPullToDomain A t x
  let w := relativeCoproductPullToComponent A t x
  have ha : w ≫ ι x = (v ≫ a) ≫ fst f hL := by
    rw [Category.assoc]
    exact (relativeCoproductPull_square A t x).symm
  have hb : w ≫ ι x = (v ≫ b) ≫ fst f hL := by
    rw [ha, Category.assoc, h₁, ← Category.assoc]
  obtain ⟨a', ha₁, ha₂⟩ := (component_isPullback f hL x).exists_lift w (v ≫ a) ha
  obtain ⟨b', hb₁, hb₂⟩ := (component_isPullback f hL x).exists_lift w (v ≫ b) hb
  have he : a' = b' := by
    apply OriginalRestrictedIntersection.hom_ext f hL (d x) (E x) (c x) (k x) U sU
    · exact ha₁.trans hb₁.symm
    · change a' ≫ componentSnd f hL x = b' ≫ componentSnd f hL x
      rw [← component_snd, ← Category.assoc, ← Category.assoc, ha₂, hb₂,
        Category.assoc, Category.assoc, h₂]
  exact ha₂.symm.trans ((congrArg (fun z ↦ z ≫
    relativeCoproductArrow (component f hL) x) he).trans hb₂)

variable {W : Over (Spec (.of R))}
  (a b : W ⟶ OrderedHilbertIdentityOriginalSection.sourceTest f hL)
  (hab : (relativeFppfSheaf f).obj.map a.op
    (OrderedHilbertIdentityOriginalSection.sourceSection f hL) =
      (relativeFppfSheaf f).obj.map b.op
        (OrderedHilbertIdentityOriginalSection.sourceSection f hL))

include hab in
/-- Equal classes remain equal on every actual first-component inverse image. -/
theorem local_class (x : (smoothHilbertSource f).left) :
    (relativeFppfSheaf f).obj.map (relativeCoproductPullToComponent A a x).op (sA x) =
      (relativeFppfSheaf f).obj.map (relativeCoproductPullToDomain A a x ≫ b).op sU := by
  rw [← OrderedHilbertIdentityOriginalSection.sourceSection_component]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  change (relativeFppfSheaf f).obj.map
    (relativeCoproductPullToComponent A a x ≫ relativeCoproductArrow A x).op _ = _
  rw [← relativeCoproductPull_square]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact congrArg ((relativeFppfSheaf f).obj.map
    (relativeCoproductPullToDomain A a x).op) hab

include hab in
/-- Every equal-class pair on every original test has a unique full relation lift. -/
theorem lift : ∃! z : W ⟶ relation f hL, z ≫ fst f hL = a ∧ z ≫ snd f hL = b := by
  have H (x : (smoothHilbertSource f).left) :=
    OriginalRestrictedIntersection.lift f hL (d x) (E x) (c x) (k x) U sU
      (relativeCoproductPullToComponent A a x)
      (relativeCoproductPullToDomain A a x ≫ b) (local_class f hL a b hab x)
  choose l hl hu using H
  let g x := l x ≫ relativeCoproductArrow (component f hL) x
  let z := relativeCoproductPullGlue A a g
  have hz (x : (smoothHilbertSource f).left) :
      relativeCoproductPullToDomain A a x ≫ z = g x :=
    relativeCoproductPullGlue_map A a g x
  have h₁ : z ≫ fst f hL = a := by
    apply relativeCoproductPull_hom_ext A a
    intro x
    rw [← Category.assoc, hz]
    change (l x ≫ _) ≫ _ = _
    rw [Category.assoc, component_fst, ← Category.assoc]
    have hx := (hl x).1
    change l x ≫ componentFst f hL x = _ at hx
    rw [hx]
    exact (relativeCoproductPull_square A a x).symm
  have h₂ : z ≫ snd f hL = b := by
    apply relativeCoproductPull_hom_ext A a
    intro x
    rw [← Category.assoc, hz]
    change (l x ≫ _) ≫ _ = _
    rw [Category.assoc, component_snd]
    exact (hl x).2
  exact ⟨z, ⟨h₁, h₂⟩, fun w hw ↦ hom_ext f hL
    (hw.1.trans h₁.symm) (hw.2.trans h₂.symm)⟩

end FLT.Mazur.OrderedHilbertIdentityOriginalRelation
