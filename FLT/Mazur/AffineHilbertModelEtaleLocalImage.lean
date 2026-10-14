/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfLocalImage
public import FLT.Mazur.AffineHilbertModelEtale

/-!
# Etale-local representatives of the original represented Picard region

The recovered etale geometry upgrades the exact local-image criterion from
fppf covers to etale covers. This constructs etale representatives of every
represented original class, on arbitrary nonreduced relative test schemes.
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
  {A : Over (Spec (.of R))}
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {T : Over (Spec (.of R))} (w : A ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
variable [LocallyOfFinitePresentation w.left]
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)
local notation "E" => modelFppfTarget f hL d V c k w hw
local notation "C" => modelFppfSource f hL d V c k w hw
local notation "π" => modelFppfProjection f hL d V c k w hw
local notation "e" => modelFppfDescendedSection f hL d V c k w hw
local notation "s₀" => modelFppfSection f hL d V c k w hw

/-- Every represented class admits actual etale local original-source representatives. -/
theorem modelFppf_represented_iff_etale_local
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
    rw [← modelFppfDescendedSection_source f hL d V c k w hw]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rw [RelativeFppfPairCover.fst_map]
  · rintro ⟨Z', t, a, ht, hs, ha⟩
    let _ := ht
    let _ := hs
    exact (modelFppf_local_representative f hL d V c k w hw t s a ha).exists

/-- On this constructed region fppf-local representability already gives etale representatives. -/
theorem modelFppf_fppf_local_iff_etale_local
    (Z : Over (Spec (.of R))) (s : (F).obj (op Z)) :
    (∃ (Z' : Over (Spec (.of R))) (t : Z' ⟶ Z) (a : Z' ⟶ C),
      Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
        (F).map t.op s = (F).map a.op s₀) ↔
      ∃ (Z' : Over (Spec (.of R))) (t : Z' ⟶ Z) (a : Z' ⟶ C),
        Etale t.left ∧ Surjective t.left ∧ (F).map t.op s = (F).map a.op s₀ := by
  rw [← modelFppf_represented_iff_fppf_local, modelFppf_represented_iff_etale_local]

end FLT.Mazur.HilbertChart.AffineRestriction
