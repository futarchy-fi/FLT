/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOrbitAtlasDescent

/-!
# Propagating effective full seed relations through complete orbits

A scheme kernel model for the full seed relation gives a scheme kernel model
for the full original orbit relation. The seed map need not be monic, and
no equality of its two coordinates is substituted for its actual relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOrbitAtlas
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S Z Q : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (s : Z ⟶ A.left) (w : Z ⟶ Q)
local notation "B" => (pullback q.left s : Scheme)
local notation "r" => pullback.fst q.left s
local notation "π" => pullback.snd q.left s
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left s
local notation "F" => doubleDomain p.left q.left b
local notation "x" => fst p.left q.left b
local notation "y" => snd p.left q.left b
local notation "E" => doubleDomain p.left q.left s
local notation "x₀" => fst p.left q.left s
local notation "y₀" => snd p.left q.left s
variable (H : IsPullback (fst p.left q.left s) (snd p.left q.left s) w w)
local notation "v" => π ≫ w
local notation "K" => (pullback v v : Scheme)
local notation "a" => pullback.fst v v
local notation "a'" => pullback.snd v v

include e H in
/-- The propagated model coequalizes every original orbit arrow, including different seeds. -/
theorem model_condition : x ≫ v = y ≫ v := pull_invariant e s w H.w

/-- Construct the full seed arrow from both independent coordinates of the model kernel. -/
def modelSeed : K ⟶ E := H.lift (a ≫ π) (a' ≫ π)
  (by simpa only [Category.assoc] using pullback.condition (f := v) (g := v))

@[reassoc]
theorem modelSeed_fst : modelSeed s w H ≫ x₀ = a ≫ π := H.lift_fst _ _ _

@[reassoc]
theorem modelSeed_snd : modelSeed s w H ≫ y₀ = a' ≫ π := H.lift_snd _ _ _

/-- Its literal original relation arrow, with the two seed morphisms retained. -/
def modelSeedArrow : K ⟶ D.left := modelSeed s w H ≫ arrow p.left q.left s

@[reassoc]
theorem modelSeedArrow_fst : modelSeedArrow s w H ≫ p.left = (a ≫ r) ≫ q.left := by
  simp only [modelSeedArrow, Category.assoc, arrow_fst, modelSeed_fst_assoc,
    pullback.condition]

@[reassoc]
theorem modelSeedArrow_snd : modelSeedArrow s w H ≫ q.left = (a' ≫ r) ≫ q.left := by
  simp only [modelSeedArrow, Category.assoc, arrow_snd, modelSeed_snd_assoc,
    pullback.condition]

/-- Recover an actual original source arrow from the seed kernel, on the entire scheme test. -/
def modelArrow : K ⟶ D.left := untransportOriginal e (a ≫ r) (a' ≫ r)
  (modelSeedArrow s w H) (modelSeedArrow_fst s w H) (modelSeedArrow_snd s w H)

@[reassoc]
theorem modelArrow_fst : modelArrow e s w H ≫ p.left = a ≫ b := by
  exact (untransportOriginal_fst e _ _ _ _ _).trans (Category.assoc _ _ _)

@[reassoc]
theorem modelArrow_snd : modelArrow e s w H ≫ q.left = a' ≫ b := by
  exact (untransportOriginal_snd e _ _ _ _ _).trans (Category.assoc _ _ _)

/-- The constructed inverse covers the full original relation, not just a same-seed subrelation. -/
def modelLift : K ⟶ F := lift p.left q.left b (modelArrow e s w H) a a'
  (modelArrow_fst e s w H) (modelArrow_snd e s w H)

@[reassoc]
theorem modelLift_fst : modelLift e s w H ≫ x = a := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem modelLift_snd : modelLift e s w H ≫ y = a' := lift_snd _ _ _ _ _ _ _ _

/-- The original relation's canonical comparison with the propagated model kernel. -/
def modelComparison : F ⟶ K := pullback.lift x y (model_condition e s w H)

@[reassoc]
theorem modelComparison_fst : modelComparison e s w H ≫ a = x := pullback.lift_fst _ _ _

@[reassoc]
theorem modelComparison_snd : modelComparison e s w H ≫ a' = y := pullback.lift_snd _ _ _

/-- A full seed kernel propagates to an actual full original scheme kernel. -/
def modelKernelIso : F ≅ K where
  hom := modelComparison e s w H
  inv := modelLift e s w H
  hom_inv_id := by
    apply SchemeRelationReanchoring.endpoint_ext e b
    · rw [Category.assoc, modelLift_fst, modelComparison_fst, Category.id_comp]
    · rw [Category.assoc, modelLift_snd, modelComparison_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, modelComparison_fst, modelLift_fst, Category.id_comp]
    · rw [Category.assoc, modelComparison_snd, modelLift_snd, Category.id_comp]

include e H in
/-- The complete original relation is the kernel of the same model after propagation. -/
theorem model_isPullback : IsPullback x y v v :=
  IsPullback.of_iso_pullback ⟨model_condition e s w H⟩ (modelKernelIso e s w H)
    (modelComparison_fst e s w H) (modelComparison_snd e s w H)

include e in
/-- An effective etale seed cover propagates to an effective etale orbit cover. -/
theorem model_cover [Etale q.left] [Etale w] [Surjective w] :
    Etale v ∧ Surjective v := by
  let _ : Surjective π := SchemeRelationSplitOrbit.projection_surjective e s
  exact ⟨inferInstance, inferInstance⟩

end FLT.Mazur.SchemeRelationOrbitAtlas
