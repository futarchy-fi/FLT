/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfLocalImage
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Natural representation of the original fppf-local Picard image

The subfunctor is defined by original source representatives on actual fppf
covers. The constructed scheme represents it on every relative scheme test;
the representing isomorphism retains the original descended Picard class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  {T : Over (Spec (.of R))} (w : A ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
variable [LocallyOfFinitePresentation w.left]
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)
local notation "E" => modelFppfTarget f hL d V c k w hw
local notation "C" => modelFppfSource f hL d V c k w hw
local notation "π" => modelFppfProjection f hL d V c k w hw
local notation "e" => modelFppfDescendedSection f hL d V c k w hw
local notation "s₀" => modelFppfSection f hL d V c k w hw

/-- Original Picard sections locally represented by the complete effective source. -/
def modelFppfLocalImage : Subfunctor ((F) ⋙ forget CommGrpCat) where
  obj Z := {s | ∃ (Z' : Over (Spec (.of R))) (t : Z' ⟶ Z.unop) (a : Z' ⟶ C),
    Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
          (F).map t.op s = (F).map a.op s₀}
  map {Z W} g s hs := by
    obtain ⟨b, hb⟩ :=
      (modelFppf_represented_iff_fppf_local f hL d V c k w hw Z.unop s).mpr hs
    apply (modelFppf_represented_iff_fppf_local f hL d V c k w hw W.unop _).mp
    refine ⟨g.unop ≫ b, ?_⟩
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp,
      ConcreteCategory.comp_apply, hb]
    rfl

/-- Every section in this actual local image has a unique original-base model point. -/
def modelFppfLocalImageEquiv (Z : Over (Spec (.of R))) :
    (Z ⟶ E) ≃ (modelFppfLocalImage f hL d V c k w hw).toFunctor.obj (op Z) :=
  Equiv.ofBijective (fun b ↦ ⟨(F).map b.op e,
    (modelFppf_represented_iff_fppf_local f hL d V c k w hw Z _).mp
      ⟨b, rfl⟩⟩) ⟨by
        intro a b hab
        exact modelFppfDescendedSection_injective f hL d V c k w hw Z
          (congrArg Subtype.val hab), by
        intro s
        obtain ⟨b, hb⟩ :=
          (modelFppf_represented_iff_fppf_local f hL d V c k w hw Z _).mpr
            s.property
        exact ⟨b, Subtype.ext hb⟩⟩

/-- A natural representation of the fppf-local image on every original-base test scheme. -/
def modelFppfLocalImageIso :
    yoneda.obj E ⋙ uliftFunctor.{1} ≅
      (modelFppfLocalImage f hL d V c k w hw).toFunctor :=
  NatIso.ofComponents (fun Z ↦
    (Equiv.ulift.trans (modelFppfLocalImageEquiv f hL d V c k w hw Z.unop)).toIso)
    (fun {Z W} g ↦ by
      apply ConcreteCategory.hom_ext
      intro b
      apply Subtype.ext
      change (F).map (g.unop ≫ b.down).op e = (F).map g ((F).map b.down.op e)
      simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply])

/-- The representation preserves precisely the descended original Picard class. -/
theorem modelFppfLocalImageIso_class (Z : Over (Spec (.of R))) (b : Z ⟶ E) :
    ((modelFppfLocalImageIso f hL d V c k w hw).hom.app (op Z) (ULift.up b)).val =
      (F).map b.op e := rfl

end FLT.Mazur.HilbertChart.AffineRestriction
