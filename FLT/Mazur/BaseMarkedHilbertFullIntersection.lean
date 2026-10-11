/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertIntersection
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Base-marked intersections are graph pullbacks of the full intersections

The constructed open is compared to the original full variable-chart
intersection. It is its scheme pullback along the prescribed base graph;
the full intersection is never replaced by this graph pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V U : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V)) (b : U ⟶ V)
  (s : (relativeFppfSheaf f).obj.obj (op U))

/-- Forgetting the prescribed base map gives a map to the full original intersection. -/
def baseMarkedHilbertToFull : baseMarkedHilbertIntersection f d V U c b s ⟶
    variableHilbertOverlap f d V c U s :=
  (variableHilbertOverlap_lift f d hL V c U s
    (baseMarkedHilbertArrow f d V U c b s)
    (baseMarkedHilbertParameter f hL d V U c b s)
    (baseMarkedHilbertParameter_class f hL d V U c b s)).choose

@[reassoc]
theorem baseMarkedHilbertToFull_test :
    baseMarkedHilbertToFull f hL d V U c b s ≫ variableHilbertOverlapToTest f d V c U s =
      baseMarkedHilbertArrow f d V U c b s :=
  (variableHilbertOverlap_lift f d hL V c U s _ _
    (baseMarkedHilbertParameter_class f hL d V U c b s)).choose_spec.1.1

@[reassoc]
theorem baseMarkedHilbertToFull_parameter :
    baseMarkedHilbertToFull f hL d V U c b s ≫
        variableHilbertOverlapToChart f d hL V c U s =
      baseMarkedHilbertParameter f hL d V U c b s :=
  (variableHilbertOverlap_lift f d hL V c U s _ _
    (baseMarkedHilbertParameter_class f hL d V U c b s)).choose_spec.1.2

/-- The original full intersection retains its independent translation-base coordinate. -/
@[reassoc]
theorem variableHilbertOverlapToChart_base :
    variableHilbertOverlapToChart f d hL V c U s ≫ variableHilbertBase f d V =
      variableHilbertOverlapArrow f d V c U s ≫ prod.snd :=
  prod.lift_fst _ _

/-- The comparison lies over the prescribed graph in the original product. -/
@[reassoc]
theorem baseMarkedHilbertToFull_graph :
    baseMarkedHilbertToFull f hL d V U c b s ≫ variableHilbertOverlapArrow f d V c U s =
      baseMarkedHilbertArrow f d V U c b s ≫ prod.lift (𝟙 U) b := by
  apply prod.hom_ext
  · simpa only [variableHilbertOverlapToTest, Category.assoc, prod.lift_fst,
      Category.comp_id] using
      baseMarkedHilbertToFull_test f hL d V U c b s
  · simp only [Category.assoc, prod.lift_snd]
    rw [← variableHilbertOverlapToChart_base f hL d V U c s, ← Category.assoc,
      baseMarkedHilbertToFull_parameter, baseMarkedHilbertParameter_base]

/-- The actual base-marked open is a scheme-theoretic graph pullback of the full intersection. -/
theorem baseMarkedHilbertFull_isPullback :
    IsPullback (baseMarkedHilbertToFull f hL d V U c b s)
      (baseMarkedHilbertArrow f d V U c b s) (variableHilbertOverlapArrow f d V c U s)
      (prod.lift (𝟙 U) b) := by
  have htest (z : PullbackCone (variableHilbertOverlapArrow f d V c U s)
      (prod.lift (𝟙 U) b)) :
      z.fst ≫ variableHilbertOverlapToTest f d V c U s = z.snd := by
    have h := congrArg (fun k ↦ k ≫ prod.fst) z.condition
    simpa only [variableHilbertOverlapToTest, Category.assoc, prod.lift_fst,
      Category.comp_id] using h
  have hbase (z : PullbackCone (variableHilbertOverlapArrow f d V c U s)
      (prod.lift (𝟙 U) b)) :
      (z.fst ≫ variableHilbertOverlapToChart f d hL V c U s) ≫
        variableHilbertBase f d V = z.snd ≫ b := by
    rw [Category.assoc, variableHilbertOverlapToChart_base, ← Category.assoc, z.condition]
    simp only [Category.assoc, prod.lift_snd]
  have hclass (z : PullbackCone (variableHilbertOverlapArrow f d V c U s)
      (prod.lift (𝟙 U) b)) :
      variableHilbertPoint f d hL V c _
        (z.fst ≫ variableHilbertOverlapToChart f d hL V c U s) =
          (relativeFppfSheaf f).obj.map z.snd.op s := by
    rw [variableHilbertPoint_natural, variableHilbertOverlap_class,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, htest]
  let lift (z : PullbackCone (variableHilbertOverlapArrow f d V c U s)
      (prod.lift (𝟙 U) b)) :=
    baseMarkedHilbertIntersection_lift f hL d V U c b s z.snd
      (z.fst ≫ variableHilbertOverlapToChart f d hL V c U s) (hbase z) (hclass z)
  have hl z : (lift z).choose ≫ baseMarkedHilbertToFull f hL d V U c b s = z.fst := by
    apply (cancel_mono (variableHilbertOverlapArrow f d V c U s)).mp
    rw [Category.assoc, baseMarkedHilbertToFull_graph, ← Category.assoc,
      (lift z).choose_spec.1.1, z.condition]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (baseMarkedHilbertToFull_graph f hL d V U c b s) (fun z ↦ (lift z).choose)
    hl (fun z ↦ (lift z).choose_spec.1.1) ?_)
  intro z q _ hq
  exact (cancel_mono (baseMarkedHilbertArrow f d V U c b s)).mp
    (hq.trans (lift z).choose_spec.1.1.symm)

/-- Etale translation bases make the original full test intersections etale. -/
instance variableHilbertOverlapToTest_etale [Etale V.hom] :
    Etale (variableHilbertOverlapToTest f d V c U s).left := by
  let _ : Etale (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  change Etale ((variableHilbertOverlapArrow f d V c U s).left ≫
    (prod.fst : prod U V ⟶ U).left)
  infer_instance

/-- Over an etale translation base, fixing the base map cuts out an actual open in the full
intersection; it does not identify the whole intersection with that open. -/
instance baseMarkedHilbertToFull_isOpenImmersion [Etale V.hom] :
    IsOpenImmersion (baseMarkedHilbertToFull f hL d V U c b s).left := by
  let _ : Etale (prod.fst : prod U V ⟶ U).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst U V]
    infer_instance
  have hg : IsOpenImmersion (prod.lift (𝟙 U) b).left :=
    UnramifiedSectionImmersion.isOpenImmersion (prod.fst : prod U V ⟶ U).left
      (prod.lift (𝟙 U) b).left (congrArg Over.Hom.left (prod.lift_fst (𝟙 U) b))
  exact MorphismProperty.of_isPullback
    ((baseMarkedHilbertFull_isPullback f hL d V U c b s).map (Over.forget _)).flip hg

end FLT.Mazur.HilbertChart
