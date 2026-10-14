/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSplitOrbit

/-!
# Full original relation kernels on split orbits

The original relation is pulled back along BOTH independent orbit endpoints
with their common new coefficient coordinate. Division of original arrows
constructs the inverse to its kernel comparison on every scheme test.
The construction requires neither flatness nor unramifiedness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSplitOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "B" => (pullback q.left a : Scheme)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "π" => pullback.snd q.left a
local notation "K" => (pullback π π : Scheme)
local notation "x" => pullback.fst π π
local notation "y" => pullback.snd π π
local notation "m" => pullback.lift p.left q.left h

/-- The new kernel remembers both old source coordinates without forgetting the new base. -/
def kernelToOld : K ⟶ pullback w w := pullback.lift (x ≫ b) (y ≫ b) (by
  simp only [Category.assoc,
    SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a]
  exact congrArg (fun g ↦ g ≫ (a ≫ w)) (pullback.condition (f := π) (g := π)))

/-- The FULL original relation on the new orbit, retaining the new coefficient coordinate. -/
def fullRelation : Scheme.{u} := pullback m (kernelToOld w h a)

/-- Its comparison to the kernel of the new projection. -/
def fullComparison : fullRelation w h a ⟶ K := pullback.snd m (kernelToOld w h a)

/-- Its unchanged original relation arrow. -/
def fullArrow : fullRelation w h a ⟶ D.left := pullback.fst m (kernelToOld w h a)

/-- Division constructs an original relation arrow from every new coefficient-equal pair. -/
def kernelArrow : K ⟶ D.left := RelativeRelationOrbit.divideOriginal e
  (x ≫ pullback.fst q.left a) (y ≫ pullback.fst q.left a) (by
    simp only [Category.assoc, pullback.condition]
    exact congrArg (fun g ↦ g ≫ a) (pullback.condition (f := π) (g := π)))

@[reassoc]
theorem kernelArrow_fst : kernelArrow e a ≫ p.left = x ≫ b :=
  RelativeRelationOrbit.divideOriginal_fst e _ _ _

@[reassoc]
theorem kernelArrow_snd : kernelArrow e a ≫ q.left = y ≫ b :=
  RelativeRelationOrbit.divideOriginal_snd e _ _ _

@[reassoc]
theorem kernelArrow_comparison : kernelArrow e a ≫ m = kernelToOld w h a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, kernelArrow_fst, kernelToOld]
  · simp only [Category.assoc, pullback.lift_snd, kernelArrow_snd, kernelToOld]

/-- A constructed inverse on the full original relation, including all nilpotent tests. -/
def kernelLift : K ⟶ fullRelation w h a :=
  pullback.lift (kernelArrow e a) (𝟙 K) (by
    rw [Category.id_comp, kernelArrow_comparison])

@[reassoc]
theorem kernelLift_comparison : kernelLift e w h a ≫ fullComparison w h a = 𝟙 K :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem kernelLift_arrow : kernelLift e w h a ≫ fullArrow w h a = kernelArrow e a :=
  pullback.lift_fst _ _ _

variable [Mono (pullback.lift p.left q.left h)]

/-- The full original relation is isomorphic to the actual new coefficient kernel. -/
def fullKernelIso : fullRelation w h a ≅ K where
  hom := fullComparison w h a
  inv := kernelLift e w h a
  hom_inv_id := by
    let _ : Mono (fullComparison w h a) :=
      inferInstanceAs (Mono (pullback.snd m (kernelToOld w h a)))
    apply (cancel_mono (fullComparison w h a)).mp
    rw [Category.assoc, kernelLift_comparison, Category.comp_id, Category.id_comp]
  inv_hom_id := kernelLift_comparison e w h a

include e in
/-- Both independent original endpoints make the orbit projection an effective kernel pair. -/
theorem fullRelation_isPullback : IsPullback
    (fullComparison w h a ≫ x) (fullComparison w h a ≫ y) π π :=
  IsPullback.of_iso_pullback
    ⟨by simp only [Category.assoc, pullback.condition]⟩ (fullKernelIso e w h a) rfl rfl

omit [Mono (pullback.lift p.left q.left h)] in
/-- Forgetting the new base recovers the actual first and second original endpoints. -/
theorem fullRelation_endpoints :
    fullArrow w h a ≫ p.left = fullComparison w h a ≫ x ≫ b ∧
    fullArrow w h a ≫ q.left = fullComparison w h a ≫ y ≫ b := by
  have he := pullback.condition (f := m) (g := kernelToOld w h a)
  constructor
  · simpa only [fullArrow, fullComparison, Category.assoc, pullback.lift_fst,
      kernelToOld] using congrArg (fun g ↦ g ≫ pullback.fst w w) he
  · simpa only [fullArrow, fullComparison, Category.assoc, pullback.lift_snd,
      kernelToOld] using congrArg (fun g ↦ g ≫ pullback.snd w w) he

end FLT.Mazur.SchemeRelationSplitOrbit
