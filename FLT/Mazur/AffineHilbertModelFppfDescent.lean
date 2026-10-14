/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelFppfPicard

/-!
# Original Picard descent on unconditionally constructed fppf regions

The actual fppf projection descends the original source section. Its descended
section separates every relative scheme test. No global flatness or
surjectivity is required of the original candidate model.
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
local notation "π" => modelFppfProjection f hL d V c k w hw
local notation "s" => modelFppfSection f hL d V c k w hw
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)

/-- Compatibility is proved on the actual scheme kernel of the constructed fppf projection. -/
theorem modelFppfSection_kernel :
    (F).map (pullback.fst π π).op s = (F).map (pullback.snd π π).op s :=
  modelFppf_equal_class f hL d V c k w hw _ _ pullback.condition

/-- The actual retained target carries a descended section of the original Picard sheaf. -/
def modelFppfDescendedSection :
    (F).obj (op (modelFppfTarget f hL d V c k w hw)) :=
  (relativePicardFppf_singleton_existsUnique f π s
    (modelFppfSection_kernel f hL d V c k w hw)).choose

/-- Pullback recovers the original section, including its original coefficient morphism. -/
theorem modelFppfDescendedSection_source :
    (F).map (π).op (modelFppfDescendedSection f hL d V c k w hw) = s :=
  (relativePicardFppf_singleton_existsUnique f π s
    (modelFppfSection_kernel f hL d V c k w hw)).choose_spec.1

/-- The whole source determines its descended section uniquely. -/
theorem modelFppfDescendedSection_unique
    (t : (F).obj (op (modelFppfTarget f hL d V c k w hw)))
    (ht : (F).map (π).op t = s) :
    t = modelFppfDescendedSection f hL d V c k w hw :=
  relativePicardFppf_singleton_injective f π
    (ht.trans (modelFppfDescendedSection_source f hL d V c k w hw).symm)

/-- The constructed open represents a subfunctor of the original Picard sheaf. -/
theorem modelFppfDescendedSection_injective (Z : Over (Spec (.of R))) :
    Function.Injective (fun a : Z ⟶ modelFppfTarget f hL d V c k w hw ↦
      (F).map a.op (modelFppfDescendedSection f hL d V c k w hw)) := by
  intro a b hab
  let t := RelativeFppfPairCover.cover π a b
  let a' := RelativeFppfPairCover.fst π a b
  let b' := RelativeFppfPairCover.snd π a b
  have ha : a' ≫ π = t ≫ a := RelativeFppfPairCover.fst_map π a b
  have hb : b' ≫ π = t ≫ b := RelativeFppfPairCover.snd_map π a b
  have he : (F).map a'.op s = (F).map b'.op s := by
    rw [← modelFppfDescendedSection_source f hL d V c k w hw]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha, hb]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg ((F).map t.op) hab
  have ht : t ≫ a = t ≫ b := by
    rw [← ha, ← hb]
    exact modelFppf_model_eq f hL d V c k w hw a' b' he
  apply (Over.forget _).map_injective
  exact (cancel_epi t.left).mp (congrArg Over.Hom.left ht)

end FLT.Mazur.HilbertChart.AffineRestriction
