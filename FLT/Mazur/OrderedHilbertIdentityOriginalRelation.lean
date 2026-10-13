/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityOriginalSection
public import FLT.Mazur.OriginalRestrictedHilbertIntersection
public import FLT.Mazur.RelativeCoproductPullCover

/-!
# The full original relation scheme on the constructed covering source

For each first component, intersect its original chart with the ENTIRE source
section. Restrict only the first parameter and form the actual coproduct.
Every second component and independent translation coordinate is retained.
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

/-- The first component against ALL second components, using their original section. -/
def component (x : (smoothHilbertSource f).left) : Over (Spec (.of R)) :=
  OriginalRestrictedIntersection.relation f hL (d x) (E x) (c x) (k x) U sU

/-- The original first endpoint in its retained affine component. -/
def componentFst (x : (smoothHilbertSource f).left) : component f hL x ⟶ A x :=
  OriginalRestrictedIntersection.fst f hL (d x) (E x) (c x) (k x) U sU

/-- The second endpoint ranges over the ENTIRE original source. -/
def componentSnd (x : (smoothHilbertSource f).left) : component f hL x ⟶ U :=
  OriginalRestrictedIntersection.snd f hL (d x) (E x) (c x) (k x) U sU

/-- Each component retains equality of the two original Picard sections. -/
theorem component_class (x : (smoothHilbertSource f).left) :
    (relativeFppfSheaf f).obj.map (componentFst f hL x).op (sA x) =
      (relativeFppfSheaf f).obj.map (componentSnd f hL x).op sU :=
  OriginalRestrictedIntersection.equal_class f hL (d x) (E x) (c x) (k x) U sU

/-- The actual scheme of all original equal-class pairs on the constructed source. -/
def relation : Over (Spec (.of R)) := relativeCoproductTest (component f hL)

/-- The first endpoint on the single original source. -/
def fst : relation f hL ⟶ U :=
  relativeCoproductMap (component f hL) A (componentFst f hL)

/-- The second endpoint on the single original source. -/
def snd : relation f hL ⟶ U :=
  Over.homMk (Sigma.desc (fun x ↦ (componentSnd f hL x).left)) (by
    apply Sigma.hom_ext
    intro x
    change Sigma.ι _ x ≫ Sigma.desc _ ≫ (U).hom = Sigma.ι _ x ≫ Sigma.desc _
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Over.w])

/-- The entire second endpoint is etale, including every mixed component. -/
instance snd_etale : Etale (snd f hL).left := by
  change Etale (Sigma.desc (fun x ↦ (componentSnd f hL x).left))
  apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
  intro x
  exact OriginalRestrictedIntersection.snd_etale f hL (d x) (E x) (c x) (k x) U sU

/-- The first endpoint retains its exact original component map. -/
theorem component_fst (x : (smoothHilbertSource f).left) :
    relativeCoproductArrow (component f hL) x ≫ fst f hL = componentFst f hL x ≫ ι x :=
  relativeCoproductArrow_map (component f hL) A (componentFst f hL) x

/-- The second endpoint retains its exact original component map. -/
theorem component_snd (x : (smoothHilbertSource f).left) :
    relativeCoproductArrow (component f hL) x ≫ snd f hL = componentSnd f hL x :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

/-- The first component pulls back to precisely its full original intersection. -/
theorem component_isPullback (x : (smoothHilbertSource f).left) :
    IsPullback (componentFst f hL x) (relativeCoproductArrow (component f hL) x)
      (ι x) (fst f hL) :=
  relativeCoproductMap_component_isPullback (component f hL) A (componentFst f hL) x

/-- The two assembled endpoints have exactly the same ORIGINAL Picard class. -/
theorem equal_class : (relativeFppfSheaf f).obj.map (fst f hL).op sU =
    (relativeFppfSheaf f).obj.map (snd f hL).op sU := by
  apply relativeCoproductSection_ext f (component f hL)
  intro x
  dsimp only [relation] at *
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    component_fst, component_snd, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    OrderedHilbertIdentityOriginalSection.sourceSection_component]
  exact component_class f hL x

end FLT.Mazur.OrderedHilbertIdentityOriginalRelation
