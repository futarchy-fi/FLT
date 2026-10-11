/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertAffineEnvelope

/-!
# The full original relation on an affine Hilbert parameter open

Restrict the parameter source, not the independent translation coordinates.
The resulting full equal-Picard-class relation is an open subscheme of the
original affine product envelope. Its universal property holds on every test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)

/-- The original Picard section on the restricted parameter source. -/
def sectionAt : (relativeFppfSheaf f).obj.obj (op A) :=
  (relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d V c)

local notation "s" => sectionAt f hL d V c k
local notation "I" => variableHilbertOverlap f d V c A s
local notation "u" => variableHilbertOverlapToChart f d hL V c A s
local notation "v" => variableHilbertOverlapToTest f d V c A s

/-- Restrict the other endpoint of the FULL intersection to the same parameter source. -/
def relation : Over (Spec (.of R)) := pullback u k

/-- The first endpoint is the independent lift of the original chart endpoint. -/
def fst : relation f hL d V c k ⟶ A := pullback.snd u k

/-- The second endpoint is the original test projection. -/
def snd : relation f hL d V c k ⟶ A := pullback.fst u k ≫ v

/-- The original two-base product envelope retains both independent coordinates. -/
def toEnvelope : relation f hL d V c k ⟶ prod A V :=
  pullback.fst u k ≫ variableHilbertOverlapArrow f d V c A s

/-- The envelope's test coordinate is precisely the second endpoint. -/
@[reassoc]
theorem toEnvelope_test : toEnvelope f hL d V c k ≫ prod.fst = snd f hL d V c k :=
  Category.assoc _ _ _

/-- The envelope's translation coordinate is the first endpoint's original base coordinate. -/
@[reassoc]
theorem toEnvelope_base : toEnvelope f hL d V c k ≫ prod.snd =
    fst f hL d V c k ≫ k ≫ variableHilbertBase f d V := by
  dsimp only [toEnvelope, fst]
  rw [Category.assoc, ← variableHilbertOverlapToChart_base f hL d V A c s,
    ← Category.assoc, pullback.condition, Category.assoc]

instance toEnvelope_isOpenImmersion [IsOpenImmersion k.left] :
    IsOpenImmersion (toEnvelope f hL d V c k).left := by
  let _ : IsOpenImmersion (pullback.fst u k).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback u k).map (Over.forget _)).flip
      (inferInstanceAs (IsOpenImmersion k.left))
  change IsOpenImmersion ((pullback.fst u k).left ≫
    (variableHilbertOverlapArrow f d V c A s).left)
  infer_instance

/-- Both restricted endpoints preserve exactly the original Picard section. -/
theorem equal_class :
    (relativeFppfSheaf f).obj.map (fst f hL d V c k).op s =
      (relativeFppfSheaf f).obj.map (snd f hL d V c k).op s := by
  change (relativeFppfSheaf f).obj.map (fst f hL d V c k).op
    ((relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d V c)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  change (relativeFppfSheaf f).obj.map (pullback.snd u k ≫ k).op _ = _
  rw [← pullback.condition, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    variableChartSection_map, variableHilbertOverlap_class]
  change _ = (relativeFppfSheaf f).obj.map (pullback.fst u k ≫ v).op s
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The endpoints distinguish maps into the entire restricted relation. -/
theorem hom_ext {T : Over (Spec (.of R))} {a b : T ⟶ relation f hL d V c k}
    (h₁ : a ≫ fst f hL d V c k = b ≫ fst f hL d V c k)
    (h₂ : a ≫ snd f hL d V c k = b ≫ snd f hL d V c k) : a = b := by
  apply pullback.hom_ext
  · apply variableHilbertOverlap_hom_ext f d hL V c A s
    · simpa only [snd, Category.assoc] using h₂
    · simpa only [fst, Category.assoc, pullback.condition] using congrArg (fun z ↦ z ≫ k) h₁
  · exact h₁

/-- Equal original classes give a unique restricted relation arrow on every original test. -/
theorem lift {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (h : (relativeFppfSheaf f).obj.map a.op s = (relativeFppfSheaf f).obj.map b.op s) :
    ∃! z : T ⟶ relation f hL d V c k,
      z ≫ fst f hL d V c k = a ∧ z ≫ snd f hL d V c k = b := by
  have h' : variableHilbertPoint f d hL V c T (a ≫ k) =
      (relativeFppfSheaf f).obj.map b.op s := by
    rw [variableHilbertPoint_natural, ← variableChartSection_map]
    exact h
  obtain ⟨q, hq, _⟩ := variableHilbertOverlap_lift f d hL V c A s b (a ≫ k) h'
  let z : T ⟶ relation f hL d V c k := pullback.lift q a hq.2
  have hz₁ : z ≫ fst f hL d V c k = a := pullback.lift_snd _ _ _
  have hz₂ : z ≫ snd f hL d V c k = b := by
    dsimp only [z, snd]
    rw [pullback.lift_fst_assoc, hq.1]
  exact ⟨z, ⟨hz₁, hz₂⟩, fun w hw ↦ hom_ext f hL d V c k
    (hw.1.trans hz₁.symm) (hw.2.trans hz₂.symm)⟩

end FLT.Mazur.HilbertChart.AffineRestriction
