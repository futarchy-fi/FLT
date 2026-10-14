/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelKernelComparison

/-!
# Original Picard recovery over arbitrary model effective opens

Retain the full source over the intrinsic effective open of any coequalizing
relative scheme model. Equality of model points is exactly equality of the
original Picard sections. No Cartesian finite-model comparison is required.
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
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "U" => KernelPairEffectiveOpen.targetOpen
  (Over.Hom.left p) (Over.Hom.left q) w.left hw
local instance modelEffectivePicardKernelMono : Mono (pullback.lift (p).left (q).left hw) :=
  modelRelationKernelMap_mono f hL d V c k w.left hw

/-- The original model projection restricted over its intrinsic effective open. -/
def modelEffectiveProjection : KernelPairEffectiveOpen.source (p).left (q).left w.left hw ⟶
    (U).toScheme := KernelPairEffectiveOpen.projection (p).left (q).left w.left hw

local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)

/-- The whole retained source keeps its literal original structural morphism. -/
def modelEffectiveOver : Over (Spec (.of R)) :=
  Over.mk (pullback.fst w.left (U).ι ≫ A.hom)

/-- Forgetting the new target coordinate preserves the actual original source. -/
def modelEffectiveToSource : modelEffectiveOver f hL d V c k w hw ⟶ A :=
  Over.homMk (pullback.fst w.left (U).ι)

local notation "b₀" => modelEffectiveToSource f hL d V c k w hw

/-- The unchanged original Picard section on the complete effective source. -/
def modelEffectiveSection : (F).obj (op (modelEffectiveOver f hL d V c k w hw)) :=
  (F).map (b₀).op (sectionAt f hL d V c k)

/-- Equal effective model points give equality of the original Picard sections. -/
theorem modelEffective_equal_class {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelEffectiveOver f hL d V c k w hw)
    (hab : a.left ≫ modelEffectiveProjection f hL d V c k w hw =
      b.left ≫ modelEffectiveProjection f hL d V c k w hw) :
    (F).map a.op (modelEffectiveSection f hL d V c k w hw) =
      (F).map b.op (modelEffectiveSection f hL d V c k w hw) := by
  obtain ⟨z, hz, _⟩ := @KernelPairEffectiveOpen.original_test_lift
    _ _ _ (p).left (q).left w.left hw
    (modelRelationKernelMap_mono f hL d V c k w.left hw) _ a.left b.left hab
  let z' : Z ⟶ relation f hL d V c k := Over.homMk z (by
    rw [← (p).w, ← Category.assoc, hz.1, Category.assoc]
    exact a.w)
  have hp : z' ≫ p = a ≫ b₀ := Over.OverMorphism.ext hz.1
  have hq : z' ≫ q = b ≫ b₀ := Over.OverMorphism.ext hz.2
  have hc := congrArg ((F).map z'.op) (equal_class f hL d V c k)
  simpa only [modelEffectiveSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, hp, hq] using hc

/-- Original Picard equality recovers equality in the constructed target, on all tests. -/
theorem modelEffective_model_eq {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelEffectiveOver f hL d V c k w hw)
    (hab : (F).map a.op (modelEffectiveSection f hL d V c k w hw) =
      (F).map b.op (modelEffectiveSection f hL d V c k w hw)) :
    a.left ≫ modelEffectiveProjection f hL d V c k w hw =
      b.left ≫ modelEffectiveProjection f hL d V c k w hw := by
  have he : (F).map (a ≫ b₀).op (sectionAt f hL d V c k) =
      (F).map (b ≫ b₀).op (sectionAt f hL d V c k) := by
    simpa only [modelEffectiveSection, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply] using hab
  obtain ⟨z, hz, _⟩ := lift f hL d V c k (a ≫ b₀) (b ≫ b₀) he
  have hp : z.left ≫ (p).left = a.left ≫ pullback.fst w.left (U).ι := congrArg Over.Hom.left hz.1
  have hq : z.left ≫ (q).left = b.left ≫ pullback.fst w.left (U).ι := congrArg Over.Hom.left hz.2
  apply (cancel_mono (U).ι).mp
  change (a.left ≫ pullback.snd w.left (U).ι) ≫ (U).ι =
    (b.left ≫ pullback.snd w.left (U).ι) ≫ (U).ι
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc,
    ← Category.assoc, ← hp, ← hq, Category.assoc, Category.assoc, hw]

/-- The effective model relation is precisely equality in the original Picard fppf sheaf. -/
theorem modelEffective_test_iff {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelEffectiveOver f hL d V c k w hw) :
    a.left ≫ modelEffectiveProjection f hL d V c k w hw =
      b.left ≫ modelEffectiveProjection f hL d V c k w hw ↔
    (F).map a.op (modelEffectiveSection f hL d V c k w hw) =
      (F).map b.op (modelEffectiveSection f hL d V c k w hw) :=
  ⟨modelEffective_equal_class f hL d V c k w hw a b,
    modelEffective_model_eq f hL d V c k w hw a b⟩

end FLT.Mazur.HilbertChart.AffineRestriction
