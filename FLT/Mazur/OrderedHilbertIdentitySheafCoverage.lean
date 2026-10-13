/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityComparisonCover
public import FLT.Mazur.OrderedHilbertIdentityKernelPair

/-!
# Original fppf sheaf coverage by the constructed effective affine sources

The full comparison intersections cover the old smooth presentation and
map to the constructed source with exactly the original Picard class.
Local surjectivity therefore transfers to the new source map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityComparisonCover
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

/-- The actual comparison arrow into the new assembled source. -/
def toSource (x : (smoothHilbertSource f).left) : intersection f hL x ⟶ U :=
  toComponent f hL x ≫ ι x

/-- The comparison preserves the ORIGINAL Picard sections on both source schemes. -/
theorem toSource_class (x : (smoothHilbertSource f).left) :
    (relativeFppfSheaf f).obj.map (toSource f hL x).op sU =
      (relativeFppfSheaf f).obj.map (toOriginal f hL x).op s := by
  rw [toSource, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    OrderedHilbertIdentityOriginalSection.sourceSection_component]
  exact original_class f hL x

/-- The comparison is an equality of natural transformations on ALL original tests. -/
theorem sourceMap_comparison (x : (smoothHilbertSource f).left) :
    uliftYoneda.{1}.map (toSource f hL x) ≫
      OrderedHilbertIdentityOriginalRelation.sourceMap f hL =
        uliftYoneda.{1}.map (toOriginal f hL x) ≫ smoothHilbertSourceMap f hL := by
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro q
  change (relativeFppfSheaf f).obj.map (q.down ≫ toSource f hL x).op sU =
    (relativeFppfSheaf f).obj.map (q.down ≫ toOriginal f hL x).op s
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [toSource_class]

/-- The constructed single source covers the ORIGINAL fppf Picard sheaf. -/
instance sourceMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (OrderedHilbertIdentityOriginalRelation.sourceMap f hL) := by
  let J := Scheme.fppfTopology.over (Spec (.of R))
  let a := Sigma.desc (fun x ↦ uliftYoneda.{1}.map (toSource f hL x))
  let b := Sigma.desc (fun x ↦ uliftYoneda.{1}.map (toOriginal f hL x))
  let _ : Presheaf.IsLocallySurjective J b :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map.{1}
      J (toOriginal f hL)).mp (covering f hL)
  have h : a ≫ OrderedHilbertIdentityOriginalRelation.sourceMap f hL =
      b ≫ smoothHilbertSourceMap f hL := by
    apply Sigma.hom_ext
    intro x
    dsimp only [a, b]
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc_assoc]
    exact sourceMap_comparison f hL x
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J h

end FLT.Mazur.OrderedHilbertIdentityComparisonCover
