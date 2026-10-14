/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEffectiveOpenLocalImage
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Representation of the original etale-local Picard image

The image is defined from actual etale-local original-source representatives.
The constructed effective scheme represents this subfunctor naturally on all
test schemes. Its inclusion keeps the original Picard section, rather than
replacing it by a separately defined quotient class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} (u : B ⟶ A) {T : Scheme}
  (i : T ⟶ (finiteKernelModel f hL d V c k).left) [Mono i] (w : B.left ⟶ T)
  (h : IsPullback u.left w (finiteKernelProjection f hL d V c k).left i)
variable [Flat w] [Surjective w]
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)
local notation "E" => monicModelEffectiveTarget f hL d V c k u i w h
local notation "C" => monicModelEffectiveOver f hL d V c k u i w h
local notation "π" => monicModelEffectiveRelativeProjection f hL d V c k u i w h
local notation "e" => monicModelEffectiveDescendedSection f hL d V c k u i w h
local notation "s₀" => monicModelEffectiveSection f hL d V c k u i w h

/-- Original Picard sections locally represented by the complete effective source. -/
def monicModelEffectiveEtaleImage : Subfunctor ((F) ⋙ forget CommGrpCat) where
  obj Z := {s | ∃ (Z' : Over (Spec (.of R))) (t : Z' ⟶ Z.unop) (a : Z' ⟶ C),
    Etale t.left ∧ Surjective t.left ∧ (F).map t.op s = (F).map a.op s₀}
  map {Z W} g s hs := by
    obtain ⟨b, hb⟩ :=
      (monicModelEffective_represented_iff_etale_local f hL d V c k u i w h Z.unop s).mpr hs
    apply (monicModelEffective_represented_iff_etale_local f hL d V c k u i w h W.unop _).mp
    refine ⟨g.unop ≫ b, ?_⟩
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp,
      ConcreteCategory.comp_apply, hb]
    rfl

/-- Every section in this actual local image has a unique original-base model point. -/
def monicModelEffectiveEtaleImageEquiv (Z : Over (Spec (.of R))) :
    (Z ⟶ E) ≃ (monicModelEffectiveEtaleImage f hL d V c k u i w h).toFunctor.obj (op Z) :=
  Equiv.ofBijective (fun b ↦ ⟨(F).map b.op e,
    (monicModelEffective_represented_iff_etale_local f hL d V c k u i w h Z _).mp
      ⟨b, rfl⟩⟩) ⟨by
        intro a b hab
        exact monicModelEffectiveDescendedSection_injective f hL d V c k u i w h Z
          (congrArg Subtype.val hab), by
        intro s
        obtain ⟨b, hb⟩ :=
          (monicModelEffective_represented_iff_etale_local f hL d V c k u i w h Z _).mpr
            s.property
        exact ⟨b, Subtype.ext hb⟩⟩

/-- A natural representation of the etale-local image on every original-base test scheme. -/
def monicModelEffectiveEtaleImageIso :
    yoneda.obj E ⋙ uliftFunctor.{1} ≅
      (monicModelEffectiveEtaleImage f hL d V c k u i w h).toFunctor :=
  NatIso.ofComponents (fun Z ↦
    (Equiv.ulift.trans (monicModelEffectiveEtaleImageEquiv f hL d V c k u i w h Z.unop)).toIso)
    (fun {Z W} g ↦ by
      apply ConcreteCategory.hom_ext
      intro b
      apply Subtype.ext
      change (F).map (g.unop ≫ b.down).op e = (F).map g ((F).map b.down.op e)
      simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply])

/-- The representation preserves precisely the descended original Picard class. -/
theorem monicModelEffectiveEtaleImageIso_class (Z : Over (Spec (.of R))) (b : Z ⟶ E) :
    ((monicModelEffectiveEtaleImageIso f hL d V c k u i w h).hom.app (op Z) (ULift.up b)).val =
      (F).map b.op e := rfl

end FLT.Mazur.HilbertChart.AffineRestriction
