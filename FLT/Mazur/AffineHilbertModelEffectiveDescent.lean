/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelEffectivePicard
public import FLT.Mazur.RelativePicardFppfSingletonDescent
public import FLT.Mazur.RelativeFppfPairCover

/-!
# Original Picard descent on arbitrary effective model opens

An actual flat surjective model projection descends the original source
section to its constructed effective open, where it separates all scheme
points functorially. This also applies to reselected joint coefficient models.
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
local notation "U" => KernelPairEffectiveOpen.targetOpen
  (Over.Hom.left (fst f hL d V c k)) (Over.Hom.left (snd f hL d V c k)) w.left hw
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)
local notation "s" => modelEffectiveSection f hL d V c k w hw

/-- The constructed target open keeps the original coefficient-base morphism. -/
def modelEffectiveTarget : Over (Spec (.of R)) :=
  Over.mk ((U).ι ≫ T.hom)

/-- The actual effective projection as a morphism over the original base. -/
def modelEffectiveRelativeProjection :
    modelEffectiveOver f hL d V c k w hw ⟶
      modelEffectiveTarget f hL d V c k w hw :=
  Over.homMk (KernelPairEffectiveOpen.projection
      (fst f hL d V c k).left (snd f hL d V c k).left w.left hw) (by
    change pullback.snd w.left (U).ι ≫ (U).ι ≫ T.hom =
      pullback.fst w.left (U).ι ≫ A.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, w.w])

local notation "π" => modelEffectiveRelativeProjection f hL d V c k w hw

instance modelEffectiveRelativeProjection_flat [Flat w.left] : Flat (π).left :=
  inferInstanceAs (Flat (KernelPairEffectiveOpen.projection
      (fst f hL d V c k).left (snd f hL d V c k).left w.left hw))

instance modelEffectiveRelativeProjection_surjective [Surjective w.left] : Surjective (π).left :=
  inferInstanceAs (Surjective (KernelPairEffectiveOpen.projection
      (fst f hL d V c k).left (snd f hL d V c k).left w.left hw))

instance modelEffectiveRelativeProjection_locallyOfFinitePresentation
    [LocallyOfFinitePresentation w.left] :
    LocallyOfFinitePresentation (π).left :=
  inferInstanceAs
    (LocallyOfFinitePresentation (KernelPairEffectiveOpen.projection
      (fst f hL d V c k).left (snd f hL d V c k).left w.left hw))

/-- Descent compatibility is proved for the actual kernel, not added as a model field. -/
theorem modelEffectiveSection_kernel :
    (F).map (pullback.fst π π).op s = (F).map (pullback.snd π π).op s :=
  modelEffective_equal_class f hL d V c k w hw _ _
    (congrArg Over.Hom.left pullback.condition)

variable [Flat w.left] [Surjective w.left] [LocallyOfFinitePresentation w.left]

/-- The constructed target open carries an actual descended original Picard section. -/
def modelEffectiveDescendedSection :
    (F).obj (op (modelEffectiveTarget f hL d V c k w hw)) :=
  (relativePicardFppf_singleton_existsUnique f π s
    (modelEffectiveSection_kernel f hL d V c k w hw)).choose

/-- Its pullback is exactly the original source section with unchanged coefficients. -/
theorem modelEffectiveDescendedSection_source :
    (F).map (π).op (modelEffectiveDescendedSection f hL d V c k w hw) = s :=
  (relativePicardFppf_singleton_existsUnique f π s
    (modelEffectiveSection_kernel f hL d V c k w hw)).choose_spec.1

/-- Descent from the whole original source determines the section uniquely. -/
theorem modelEffectiveDescendedSection_unique
    (t : (F).obj (op (modelEffectiveTarget f hL d V c k w hw)))
    (ht : (F).map (π).op t = s) :
    t = modelEffectiveDescendedSection f hL d V c k w hw :=
  relativePicardFppf_singleton_injective f π
    (ht.trans (modelEffectiveDescendedSection_source f hL d V c k w hw).symm)

/-- The constructed target represents a subfunctor of the original Picard sheaf. -/
theorem modelEffectiveDescendedSection_injective (Z : Over (Spec (.of R))) :
    Function.Injective (fun a : Z ⟶ modelEffectiveTarget f hL d V c k w hw ↦
      (F).map a.op (modelEffectiveDescendedSection f hL d V c k w hw)) := by
  intro a b hab
  let t := RelativeFppfPairCover.cover π a b
  let a' := RelativeFppfPairCover.fst π a b
  let b' := RelativeFppfPairCover.snd π a b
  have ha : a' ≫ π = t ≫ a := RelativeFppfPairCover.fst_map π a b
  have hb : b' ≫ π = t ≫ b := RelativeFppfPairCover.snd_map π a b
  have he : (F).map a'.op s = (F).map b'.op s := by
    rw [← modelEffectiveDescendedSection_source f hL d V c k w hw]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha, hb]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg ((F).map t.op) hab
  have ht : t ≫ a = t ≫ b := by
    rw [← ha, ← hb]
    exact Over.OverMorphism.ext
      (modelEffective_model_eq f hL d V c k w hw a' b' he)
  apply (Over.forget _).map_injective
  exact (cancel_epi t.left).mp (congrArg Over.Hom.left ht)

end FLT.Mazur.HilbertChart.AffineRestriction
