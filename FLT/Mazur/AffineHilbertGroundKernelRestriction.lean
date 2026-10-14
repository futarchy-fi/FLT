/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelKernelComparison

/-!
# Restricting an actual ground kernel in a proper-family Picard chart

If the full Picard relation on a parameter source is its ground kernel, the
same holds after any relative source restriction. The inverse is constructed
from equality of the actual Picard sections on arbitrary scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  (H : IsPullback (fst f hL d V c k).left (snd f hL d V c k).left A.hom A.hom)
  {B : Over (Spec (.of R))} (v : B ⟶ A)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "p'" => fst f hL d V c (v ≫ k)
local notation "q'" => snd f hL d V c (v ≫ k)

include H in
/-- Ground equality constructs equality of the original restricted Picard sections. -/
theorem groundKernelRestriction_class {T : Over (Spec (.of R))} (x y : T ⟶ B) :
    (relativeFppfSheaf f).obj.map x.op (sectionAt f hL d V c (v ≫ k)) =
      (relativeFppfSheaf f).obj.map y.op (sectionAt f hL d V c (v ≫ k)) := by
  have hh : (x ≫ v).left ≫ A.hom = (y ≫ v).left ≫ A.hom :=
    (x ≫ v).w.trans (y ≫ v).w.symm
  let z : T ⟶ relation f hL d V c k :=
    Over.homMk (H.lift (x ≫ v).left (y ≫ v).left hh) (by
      rw [← (p).w, H.lift_fst_assoc, (x ≫ v).w])
  have hz := equal_class_natural f hL d V c k z
  have hx : z ≫ p = x ≫ v := Over.OverMorphism.ext (H.lift_fst _ _ hh)
  have hy : z ≫ q = y ≫ v := Over.OverMorphism.ext (H.lift_snd _ _ hh)
  rw [hx, hy] at hz
  simpa only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hz

/-- Both endpoints of the nested relation keep their literal ground coordinate. -/
theorem groundKernelRestriction_condition : (p').left ≫ B.hom = (q').left ≫ B.hom :=
  (p').w.trans (q').w.symm

local notation "K" => (pullback B.hom B.hom : Scheme)
local notation "m" => modelRelationKernelMap f hL d V c (v ≫ k) B.hom
  (groundKernelRestriction_condition f hL d V c k v)

/-- Construct an inverse on the full nested scheme kernel, retaining nilpotent tests. -/
def groundKernelRestrictionInverse : K ⟶ (relation f hL d V c (v ≫ k)).left := by
  let T : Over (Spec (.of R)) := Over.mk (pullback.fst B.hom B.hom ≫ B.hom)
  let x : T ⟶ B := Over.homMk (pullback.fst B.hom B.hom)
  let y : T ⟶ B := Over.homMk (pullback.snd B.hom B.hom) pullback.condition.symm
  exact (arrow f hL d V c (v ≫ k) x y
    (groundKernelRestriction_class f hL d V c k H v x y)).left

@[reassoc]
theorem groundKernelRestrictionInverse_fst :
    groundKernelRestrictionInverse f hL d V c k H v ≫ (p').left =
      pullback.fst B.hom B.hom := by
  exact congrArg Over.Hom.left (arrow_fst f hL d V c (v ≫ k) _ _ _)

@[reassoc]
theorem groundKernelRestrictionInverse_snd :
    groundKernelRestrictionInverse f hL d V c k H v ≫ (q').left =
      pullback.snd B.hom B.hom := by
  exact congrArg Over.Hom.left (arrow_snd f hL d V c (v ≫ k) _ _ _)

/-- The independently rebuilt nested Picard relation is exactly its ground kernel. -/
def groundKernelRestrictionIso : (relation f hL d V c (v ≫ k)).left ≅ K where
  hom := m
  inv := groundKernelRestrictionInverse f hL d V c k H v
  hom_inv_id := by
    apply (cancel_mono m).mp
    have hi : groundKernelRestrictionInverse f hL d V c k H v ≫ m = 𝟙 K := by
      apply pullback.hom_ext
      · rw [Category.assoc, modelRelationKernelMap_fst,
          groundKernelRestrictionInverse_fst, Category.id_comp]
      · rw [Category.assoc, modelRelationKernelMap_snd,
          groundKernelRestrictionInverse_snd, Category.id_comp]
    rw [Category.assoc, hi, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, modelRelationKernelMap_fst,
        groundKernelRestrictionInverse_fst, Category.id_comp]
    · rw [Category.assoc, modelRelationKernelMap_snd,
        groundKernelRestrictionInverse_snd, Category.id_comp]

include H in
/-- Arbitrary source restrictions preserve the complete ground kernel square. -/
theorem groundKernelRestriction_isPullback : IsPullback (p').left (q').left B.hom B.hom :=
  IsPullback.of_iso_pullback ⟨groundKernelRestriction_condition f hL d V c k v⟩
    (groundKernelRestrictionIso f hL d V c k H v)
    (modelRelationKernelMap_fst f hL d V c (v ≫ k) _ _)
    (modelRelationKernelMap_snd f hL d V c (v ≫ k) _ _)

end FLT.Mazur.HilbertChart.AffineRestriction
