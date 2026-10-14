/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEffectiveOpenEtale

/-!
# Exact etale-local image of the constructed Picard model

An original Picard section is represented by the effective target precisely
when it is etale-locally the section of its complete original source. The
representing morphism is unique and keeps the original coefficient base.
This identifies a represented subfunctor, without claiming global coverage.
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

/-- Actual fppf-local source representatives descend to a unique relative model morphism. -/
theorem monicModelEffective_local_representative
    {Z Z' : Over (Spec (.of R))} (t : Z' ⟶ Z)
    [Flat t.left] [LocallyOfFinitePresentation t.left] [Surjective t.left]
    (s : (F).obj (op Z)) (a : Z' ⟶ C) (ha : (F).map t.op s = (F).map a.op s₀) :
    ∃! b : Z ⟶ E, (F).map b.op e = s := by
  let r := a ≫ π
  have hr : (F).map r.op e = (F).map t.op s := by
    simp only [r, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      monicModelEffectiveDescendedSection_source, ha]
  have hc : pullback.fst t t ≫ r = pullback.snd t t ≫ r := by
    apply monicModelEffectiveDescendedSection_injective f hL d V c k u i w h
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hr]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      pullback.condition]
  let b := RelativeFppfSchemeCover.descend t r hc
  have hb : (F).map b.op e = s := by
    apply relativePicardFppf_singleton_injective f t
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      RelativeFppfSchemeCover.descend_source]
    exact hr
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  exact monicModelEffectiveDescendedSection_injective f hL d V c k u i w h Z
    (hb'.trans hb.symm)

/-- The represented subfunctor is exactly the etale-local image of the whole source. -/
theorem monicModelEffective_represented_iff_etale_local
    (Z : Over (Spec (.of R))) (s : (F).obj (op Z)) :
    (∃ b : Z ⟶ E, (F).map b.op e = s) ↔
      ∃ (Z' : Over (Spec (.of R))) (t : Z' ⟶ Z) (a : Z' ⟶ C),
        Etale t.left ∧ Surjective t.left ∧ (F).map t.op s = (F).map a.op s₀ := by
  constructor
  · rintro ⟨b, rfl⟩
    let Z' := RelativeFppfPairCover.source π b b
    let t := RelativeFppfPairCover.cover π b b
    let a := RelativeFppfPairCover.fst π b b
    refine ⟨Z', t, a, inferInstance, inferInstance, ?_⟩
    rw [← monicModelEffectiveDescendedSection_source f hL d V c k u i w h]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rw [RelativeFppfPairCover.fst_map]
  · rintro ⟨Z', t, a, ht, hs, ha⟩
    let _ := ht
    let _ := hs
    exact (monicModelEffective_local_representative f hL d V c k u i w h t s a ha).exists

end FLT.Mazur.HilbertChart.AffineRestriction
