/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationArrowCalculus
public import FLT.Mazur.SchemeRelationEtaleBranchPropagation

/-!
# Full scheme kernel lifts on a propagated monic seed

A seed monic over the coefficient target identifies its two coordinates on
any coefficient kernel test. Division of the original relation arrows then
constructs a lift to the full relation. No kernel point coverage is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left) [Mono (a ≫ w)]
local notation "B" => (pullback q.left a : Scheme)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "r" => pullback.fst q.left a
local notation "s" => pullback.snd q.left a
variable {Y : Scheme.{u}} (x y : Y ⟶ pullback q.left a)

include h
/-- Monicity identifies the full seed morphisms, including their nilpotent coordinates. -/
theorem seed_eq (hxy : x ≫ b ≫ w = y ≫ b ≫ w) : x ≫ s = y ≫ s := by
  apply (cancel_mono (a ≫ w)).mp
  simpa only [Category.assoc,
    ← SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a] using hxy

/-- The two original arrows now have the same actual second endpoint. -/
theorem endpoint_eq (hxy : x ≫ b ≫ w = y ≫ b ≫ w) : (x ≫ r) ≫ q.left = (y ≫ r) ≫ q.left := by
  simp only [Category.assoc, pullback.condition]
  exact congrArg (fun z ↦ z ≫ a) (seed_eq w h a x y hxy)

/-- Divide original arrows to construct a full relation lift on every scheme kernel test. -/
def lift (hxy : x ≫ b ≫ w = y ≫ b ≫ w) : Y ⟶ D.left :=
  RelativeRelationOrbit.divideOriginal e (x ≫ r) (y ≫ r) (endpoint_eq w h a x y hxy)

@[reassoc]
theorem lift_fst (hxy : x ≫ b ≫ w = y ≫ b ≫ w) : lift e w h a x y hxy ≫ p.left = x ≫ b := by
  rw [lift, RelativeRelationOrbit.divideOriginal_fst]
  rfl

@[reassoc]
theorem lift_snd (hxy : x ≫ b ≫ w = y ≫ b ≫ w) : lift e w h a x y hxy ≫ q.left = y ≫ b := by
  rw [lift, RelativeRelationOrbit.divideOriginal_snd]
  rfl

/-- The lift is an inverse on the original candidate kernel, not only on its carrier. -/
theorem lift_kernel (hxy : x ≫ b ≫ w = y ≫ b ≫ w) :
    lift e w h a x y hxy ≫ pullback.lift p.left q.left h =
    pullback.lift (x ≫ b) (y ≫ b)
      (by simpa only [Category.assoc] using hxy) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, lift_fst]
  · simp only [Category.assoc, pullback.lift_snd, lift_snd]

end FLT.Mazur.SchemeRelationMonicSeedKernel
