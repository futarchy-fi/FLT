/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEffectiveTargetOpen

/-!
# Original Picard-section recovery on constructed effective target opens

The actual restricted source keeps its original base and original Picard
section. Two arbitrary tests have the same model point exactly when their
original Picard sections agree. The constructed open is not claimed to cover.
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
local notation "p" => fst f hL d V c (u ≫ k)
local notation "q" => snd f hL d V c (u ≫ k)
local notation "H" => monicModelRelation_condition f hL d V c k u i w h
local notation "U" => monicModelEffectiveTargetOpen f hL d V c k u i w h
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)

/-- The whole retained source keeps its literal original structural morphism. -/
def monicModelEffectiveOver : Over (Spec (.of R)) :=
  Over.mk (pullback.fst w (U).ι ≫ B.hom)

/-- Forgetting the new target coordinate preserves the actual original source. -/
def monicModelEffectiveToSource : monicModelEffectiveOver f hL d V c k u i w h ⟶ B :=
  Over.homMk (pullback.fst w (U).ι)

local notation "b₀" => monicModelEffectiveToSource f hL d V c k u i w h

/-- The unchanged original Picard section on the complete effective source. -/
def monicModelEffectiveSection : (F).obj (op (monicModelEffectiveOver f hL d V c k u i w h)) :=
  (F).map (b₀).op (sectionAt f hL d V c (u ≫ k))

/-- Equal effective model points give equality of the original Picard sections. -/
theorem monicModelEffective_equal_class {Z : Over (Spec (.of R))}
    (a b : Z ⟶ monicModelEffectiveOver f hL d V c k u i w h)
    (hab : a.left ≫ monicModelEffectiveProjection f hL d V c k u i w h =
      b.left ≫ monicModelEffectiveProjection f hL d V c k u i w h) :
    (F).map a.op (monicModelEffectiveSection f hL d V c k u i w h) =
      (F).map b.op (monicModelEffectiveSection f hL d V c k u i w h) := by
  obtain ⟨z, hz, _⟩ := @KernelPairEffectiveOpen.original_test_lift _ _ _ (p).left (q).left w H
    (monicModelRelationKernelMap_mono f hL d V c k u i w h) _ a.left b.left hab
  let z' : Z ⟶ relation f hL d V c (u ≫ k) := Over.homMk z (by
    rw [← (p).w, ← Category.assoc, hz.1, Category.assoc]
    exact a.w)
  have hp : z' ≫ p = a ≫ b₀ := Over.OverMorphism.ext hz.1
  have hq : z' ≫ q = b ≫ b₀ := Over.OverMorphism.ext hz.2
  have hc := congrArg ((F).map z'.op) (equal_class f hL d V c (u ≫ k))
  simpa only [monicModelEffectiveSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, hp, hq] using hc

/-- Original Picard equality recovers equality in the constructed target, on all tests. -/
theorem monicModelEffective_model_eq {Z : Over (Spec (.of R))}
    (a b : Z ⟶ monicModelEffectiveOver f hL d V c k u i w h)
    (hab : (F).map a.op (monicModelEffectiveSection f hL d V c k u i w h) =
      (F).map b.op (monicModelEffectiveSection f hL d V c k u i w h)) :
    a.left ≫ monicModelEffectiveProjection f hL d V c k u i w h =
      b.left ≫ monicModelEffectiveProjection f hL d V c k u i w h := by
  have he : (F).map (a ≫ b₀).op (sectionAt f hL d V c (u ≫ k)) =
      (F).map (b ≫ b₀).op (sectionAt f hL d V c (u ≫ k)) := by
    simpa only [monicModelEffectiveSection, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply] using hab
  obtain ⟨z, hz, _⟩ := lift f hL d V c (u ≫ k) (a ≫ b₀) (b ≫ b₀) he
  have hp : z.left ≫ (p).left = a.left ≫ pullback.fst w (U).ι := congrArg Over.Hom.left hz.1
  have hq : z.left ≫ (q).left = b.left ≫ pullback.fst w (U).ι := congrArg Over.Hom.left hz.2
  apply (cancel_mono (U).ι).mp
  change (a.left ≫ pullback.snd w (U).ι) ≫ (U).ι =
    (b.left ≫ pullback.snd w (U).ι) ≫ (U).ι
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc,
    ← Category.assoc, ← hp, ← hq, Category.assoc, Category.assoc, H]

/-- The effective model relation is precisely equality in the original Picard fppf sheaf. -/
theorem monicModelEffective_test_iff {Z : Over (Spec (.of R))}
    (a b : Z ⟶ monicModelEffectiveOver f hL d V c k u i w h) :
    a.left ≫ monicModelEffectiveProjection f hL d V c k u i w h =
      b.left ≫ monicModelEffectiveProjection f hL d V c k u i w h ↔
    (F).map a.op (monicModelEffectiveSection f hL d V c k u i w h) =
      (F).map b.op (monicModelEffectiveSection f hL d V c k u i w h) :=
  ⟨monicModelEffective_equal_class f hL d V c k u i w h a b,
    monicModelEffective_model_eq f hL d V c k u i w h a b⟩

end FLT.Mazur.HilbertChart.AffineRestriction
