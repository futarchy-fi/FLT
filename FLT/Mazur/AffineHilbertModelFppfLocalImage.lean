/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfDescent
public import FLT.Mazur.RelativeFppfSchemeCover

/-!
# Exact fppf-local image of the actual constructed Picard region

A section of the original Picard sheaf is represented by the constructed target
exactly when it is fppf-locally represented by its whole original source. The
unique representing map preserves the original coefficient base.
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

/-- Actual fppf-local source representatives descend to a unique relative model morphism. -/
theorem modelFppf_local_representative
    {Z Z' : Over (Spec (.of R))} (t : Z' ⟶ Z)
    [Flat t.left] [LocallyOfFinitePresentation t.left] [Surjective t.left]
    (s : (F).obj (op Z)) (a : Z' ⟶ C) (ha : (F).map t.op s = (F).map a.op s₀) :
    ∃! b : Z ⟶ E, (F).map b.op e = s := by
  let r := a ≫ π
  have hr : (F).map r.op e = (F).map t.op s := by
    simp only [r, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      modelFppfDescendedSection_source, ha]
  have hc : pullback.fst t t ≫ r = pullback.snd t t ≫ r := by
    apply modelFppfDescendedSection_injective f hL d V c k w hw
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
  exact modelFppfDescendedSection_injective f hL d V c k w hw Z
    (hb'.trans hb.symm)

/-- The represented subfunctor is exactly the fppf-local image of the whole source. -/
theorem modelFppf_represented_iff_fppf_local
    (Z : Over (Spec (.of R))) (s : (F).obj (op Z)) :
    (∃ b : Z ⟶ E, (F).map b.op e = s) ↔
      ∃ (Z' : Over (Spec (.of R))) (t : Z' ⟶ Z) (a : Z' ⟶ C),
        Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
          (F).map t.op s = (F).map a.op s₀ := by
  constructor
  · rintro ⟨b, rfl⟩
    let Z' := RelativeFppfPairCover.source π b b
    let t := RelativeFppfPairCover.cover π b b
    let a := RelativeFppfPairCover.fst π b b
    refine ⟨Z', t, a, inferInstance, inferInstance, inferInstance, ?_⟩
    rw [← modelFppfDescendedSection_source f hL d V c k w hw]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rw [RelativeFppfPairCover.fst_map]
  · rintro ⟨Z', t, a, ht, hl, hs, ha⟩
    let _ := ht
    let _ := hl
    let _ := hs
    exact (modelFppf_local_representative f hL d V c k w hw t s a ha).exists

end FLT.Mazur.HilbertChart.AffineRestriction
