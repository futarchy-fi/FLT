/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChartRelation

/-!
# Full intersections of a restricted original chart with any original test

Only the chart endpoint is restricted. The other endpoint is an arbitrary
original Picard section, so mixed components and independent translation
coordinates remain in the represented relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.OriginalRestrictedIntersection
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)

variable (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))
local notation "t" => AffineRestriction.sectionAt f hL d V c k
local notation "I" => variableHilbertOverlap f d V c U s
local notation "u" => variableHilbertOverlapToChart f d hL V c U s
local notation "v" => variableHilbertOverlapToTest f d V c U s

/-- Restrict the chart endpoint of the FULL intersection to the supplied parameter source. -/
def relation : Over (Spec (.of R)) := pullback u k

/-- The first endpoint is the independent lift of the original chart endpoint. -/
def fst : relation f hL d V c k U s ⟶ A := pullback.snd u k

/-- The second endpoint is the original test projection. -/
def snd : relation f hL d V c k U s ⟶ U := pullback.fst u k ≫ v

/-- The original two-base product envelope retains both independent coordinates. -/
def toEnvelope : relation f hL d V c k U s ⟶ prod U V :=
  pullback.fst u k ≫ variableHilbertOverlapArrow f d V c U s

/-- The envelope's test coordinate is precisely the second endpoint. -/
@[reassoc]
theorem toEnvelope_test : toEnvelope f hL d V c k U s ≫ prod.fst = snd f hL d V c k U s :=
  Category.assoc _ _ _

/-- The envelope's translation coordinate is the first endpoint's original base coordinate. -/
@[reassoc]
theorem toEnvelope_base : toEnvelope f hL d V c k U s ≫ prod.snd =
    fst f hL d V c k U s ≫ k ≫ variableHilbertBase f d V := by
  dsimp only [toEnvelope, fst]
  rw [Category.assoc, ← variableHilbertOverlapToChart_base f hL d V U c s,
    ← Category.assoc, pullback.condition, Category.assoc]

instance toEnvelope_isOpenImmersion [IsOpenImmersion k.left] :
    IsOpenImmersion (toEnvelope f hL d V c k U s).left := by
  let _ : IsOpenImmersion (pullback.fst u k).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback u k).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion k.left))
  change IsOpenImmersion ((pullback.fst u k).left ≫
    (variableHilbertOverlapArrow f d V c U s).left)
  infer_instance

/-- Etale translation and open parameter restriction give an etale second endpoint. -/
instance snd_etale [Etale V.hom] [IsOpenImmersion k.left] :
    Etale (snd f hL d V c k U s).left := by
  let _ : IsOpenImmersion (pullback.fst u k).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback u k).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion k.left))
  change Etale ((pullback.fst u k).left ≫ (v).left)
  infer_instance

/-- Both restricted endpoints preserve exactly the original Picard section. -/
theorem equal_class :
    (relativeFppfSheaf f).obj.map (fst f hL d V c k U s).op t =
      (relativeFppfSheaf f).obj.map (snd f hL d V c k U s).op s := by
  change (relativeFppfSheaf f).obj.map (fst f hL d V c k U s).op
    ((relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d V c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  change (relativeFppfSheaf f).obj.map (pullback.snd u k ≫ k).op _ = _
  rw [← pullback.condition, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    variableChartSection_map, variableHilbertOverlap_class]
  change _ = (relativeFppfSheaf f).obj.map (pullback.fst u k ≫ v).op s
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The endpoints distinguish maps into the entire restricted relation. -/
theorem hom_ext {T : Over (Spec (.of R))} {a b : T ⟶ relation f hL d V c k U s}
    (h₁ : a ≫ fst f hL d V c k U s = b ≫ fst f hL d V c k U s)
    (h₂ : a ≫ snd f hL d V c k U s = b ≫ snd f hL d V c k U s) : a = b := by
  apply pullback.hom_ext
  · apply variableHilbertOverlap_hom_ext f d hL V c U s
    · simpa only [snd, Category.assoc] using h₂
    · simpa only [fst, Category.assoc, pullback.condition] using congrArg (fun z ↦ z ≫ k) h₁
  · exact h₁

/-- Equal original classes give a unique mixed intersection arrow on every original test. -/
theorem lift {T : Over (Spec (.of R))} (a : T ⟶ A) (b : T ⟶ U)
    (h : (relativeFppfSheaf f).obj.map a.op t = (relativeFppfSheaf f).obj.map b.op s) :
    ∃! z : T ⟶ relation f hL d V c k U s,
      z ≫ fst f hL d V c k U s = a ∧ z ≫ snd f hL d V c k U s = b := by
  have h' : variableHilbertPoint f d hL V c T (a ≫ k) =
      (relativeFppfSheaf f).obj.map b.op s := by
    rw [variableHilbertPoint_natural, ← variableChartSection_map]
    exact h
  obtain ⟨q, hq, _⟩ := variableHilbertOverlap_lift f d hL V c U s b (a ≫ k) h'
  let z : T ⟶ relation f hL d V c k U s := pullback.lift q a hq.2
  have hz₁ : z ≫ fst f hL d V c k U s = a := pullback.lift_snd _ _ _
  have hz₂ : z ≫ snd f hL d V c k U s = b := by
    dsimp only [z, snd]
    rw [pullback.lift_fst_assoc, hq.1]
  exact ⟨z, ⟨hz₁, hz₂⟩, fun w hw ↦ hom_ext f hL d V c k U s
    (hw.1.trans hz₁.symm) (hw.2.trans hz₂.symm)⟩

end FLT.Mazur.HilbertChart.OriginalRestrictedIntersection
