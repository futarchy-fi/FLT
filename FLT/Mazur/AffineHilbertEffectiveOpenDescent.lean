/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEffectiveOpenPicard
public import FLT.Mazur.RelativePicardFppfSingletonDescent
public import FLT.Mazur.RelativeFppfPairCover

/-!
# Actual Picard sections descended to the constructed target opens

For an actual flat surjective model projection, the unchanged source section
descends to the constructed effective open. It distinguishes all scheme tests.
Coverage of the original quotient target remains a separate geometric task.
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
local notation "U" => monicModelEffectiveTargetOpen f hL d V c k u i w h
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)
local notation "s" => monicModelEffectiveSection f hL d V c k u i w h

/-- The constructed target open keeps the original coefficient-base morphism. -/
def monicModelEffectiveTarget : Over (Spec (.of R)) :=
  Over.mk ((U).ι ≫ i ≫ (finiteKernelModel f hL d V c k).hom)

/-- The actual effective projection as a morphism over the original base. -/
def monicModelEffectiveRelativeProjection :
    monicModelEffectiveOver f hL d V c k u i w h ⟶
      monicModelEffectiveTarget f hL d V c k u i w h :=
  Over.homMk (monicModelEffectiveProjection f hL d V c k u i w h) (by
    change pullback.snd w (U).ι ≫ (U).ι ≫ i ≫
      (finiteKernelModel f hL d V c k).hom = pullback.fst w (U).ι ≫ B.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc,
      ← Category.assoc w, ← h.w, Category.assoc, (finiteKernelProjection f hL d V c k).w,
      u.w])

local notation "π" => monicModelEffectiveRelativeProjection f hL d V c k u i w h

instance monicModelEffectiveRelativeProjection_flat [Flat w] : Flat (π).left :=
  inferInstanceAs (Flat (monicModelEffectiveProjection f hL d V c k u i w h))

instance monicModelEffectiveRelativeProjection_surjective [Surjective w] : Surjective (π).left :=
  inferInstanceAs (Surjective (monicModelEffectiveProjection f hL d V c k u i w h))

instance monicModelEffectiveRelativeProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (π).left :=
  inferInstanceAs
    (LocallyOfFinitePresentation (monicModelEffectiveProjection f hL d V c k u i w h))

/-- Descent compatibility is proved for the actual kernel, not added as a model field. -/
theorem monicModelEffectiveSection_kernel :
    (F).map (pullback.fst π π).op s = (F).map (pullback.snd π π).op s :=
  monicModelEffective_equal_class f hL d V c k u i w h _ _
    (congrArg Over.Hom.left pullback.condition)

variable [Flat w] [Surjective w]

/-- The constructed target open carries an actual descended original Picard section. -/
def monicModelEffectiveDescendedSection :
    (F).obj (op (monicModelEffectiveTarget f hL d V c k u i w h)) :=
  (relativePicardFppf_singleton_existsUnique f π s
    (monicModelEffectiveSection_kernel f hL d V c k u i w h)).choose

/-- Its pullback is exactly the original source section with unchanged coefficients. -/
theorem monicModelEffectiveDescendedSection_source :
    (F).map (π).op (monicModelEffectiveDescendedSection f hL d V c k u i w h) = s :=
  (relativePicardFppf_singleton_existsUnique f π s
    (monicModelEffectiveSection_kernel f hL d V c k u i w h)).choose_spec.1

/-- Descent from the whole original source determines the section uniquely. -/
theorem monicModelEffectiveDescendedSection_unique
    (t : (F).obj (op (monicModelEffectiveTarget f hL d V c k u i w h)))
    (ht : (F).map (π).op t = s) :
    t = monicModelEffectiveDescendedSection f hL d V c k u i w h :=
  relativePicardFppf_singleton_injective f π
    (ht.trans (monicModelEffectiveDescendedSection_source f hL d V c k u i w h).symm)

/-- The constructed target represents a subfunctor of the original Picard sheaf. -/
theorem monicModelEffectiveDescendedSection_injective (Z : Over (Spec (.of R))) :
    Function.Injective (fun a : Z ⟶ monicModelEffectiveTarget f hL d V c k u i w h ↦
      (F).map a.op (monicModelEffectiveDescendedSection f hL d V c k u i w h)) := by
  intro a b hab
  let t := RelativeFppfPairCover.cover π a b
  let a' := RelativeFppfPairCover.fst π a b
  let b' := RelativeFppfPairCover.snd π a b
  have ha : a' ≫ π = t ≫ a := RelativeFppfPairCover.fst_map π a b
  have hb : b' ≫ π = t ≫ b := RelativeFppfPairCover.snd_map π a b
  have he : (F).map a'.op s = (F).map b'.op s := by
    rw [← monicModelEffectiveDescendedSection_source f hL d V c k u i w h]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha, hb]
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg ((F).map t.op) hab
  have ht : t ≫ a = t ≫ b := by
    rw [← ha, ← hb]
    exact Over.OverMorphism.ext
      (monicModelEffective_model_eq f hL d V c k u i w h a' b' he)
  apply (Over.forget _).map_injective
  exact (cancel_epi t.left).mp (congrArg Over.Hom.left ht)

end FLT.Mazur.HilbertChart.AffineRestriction
