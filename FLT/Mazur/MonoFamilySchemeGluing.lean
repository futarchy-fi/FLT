/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Gluing a family of monomorphisms with open intersections

The full categorical intersections supply gluing data without requiring the
family to cover its ambient scheme. This applies to compatible local closed
subschemes on an ambient open cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.MonoFamilyGluing

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}}
variable (f : ∀ i, U i ⟶ X)

/-- The cyclic transition between the actual triple intersections. -/
def cyclicTripleMap (x y z : ι) :
    pullback (pullback.fst (f x) (f y)) (pullback.fst (f x) (f z)) ⟶
      pullback (pullback.fst (f y) (f z)) (pullback.fst (f y) (f x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- The first chart projection of the cyclic transition. -/
@[simp, reassoc]
theorem cyclicTripleMap_fst_fst (x y z : ι) :
    cyclicTripleMap f x y z ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta cyclicTripleMap; simp

set_option backward.isDefEq.respectTransparency false in
/-- The third chart projection of the cyclic transition. -/
@[simp, reassoc]
theorem cyclicTripleMap_fst_snd (x y z : ι) :
    cyclicTripleMap f x y z ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta cyclicTripleMap; simp

set_option backward.isDefEq.respectTransparency false in
/-- The second occurrence of the second chart projection. -/
@[simp, reassoc]
theorem cyclicTripleMap_snd_fst (x y z : ι) :
    cyclicTripleMap f x y z ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta cyclicTripleMap; simp

set_option backward.isDefEq.respectTransparency false in
/-- The cyclic transition retains the first chart projection. -/
@[simp, reassoc]
theorem cyclicTripleMap_snd_snd (x y z : ι) :
    cyclicTripleMap f x y z ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta cyclicTripleMap; simp

/-- Three cyclic transitions preserve the first overlap projection. -/
theorem cyclicTripleCocycle_fst (x y z : ι) :
    cyclicTripleMap f x y z ≫ cyclicTripleMap f y z x ≫ cyclicTripleMap f z x y ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp

/-- Three cyclic transitions preserve the second overlap projection. -/
theorem cyclicTripleCocycle_snd (x y z : ι) :
    cyclicTripleMap f x y z ≫ cyclicTripleMap f y z x ≫ cyclicTripleMap f z x y ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  apply pullback.hom_ext <;> simp [pullback.condition]

/-- The actual triple transitions satisfy the cocycle identity. -/
theorem cyclicTripleCocycle (x y z : ι) :
    cyclicTripleMap f x y z ≫ cyclicTripleMap f y z x ≫ cyclicTripleMap f z x y = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply cyclicTripleCocycle_fst
  · apply cyclicTripleCocycle_snd

variable [∀ i, Mono (f i)]
variable [∀ i j, IsOpenImmersion (pullback.fst (f i) (f j))]

/-- The actual gluing datum of a monomorphism family with open intersections. -/
def glueData : Scheme.GlueData where
  J := ι
  U := U
  V p := pullback (f p.1) (f p.2)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id _ := by simp
  t' i j k := cyclicTripleMap f i j k
  t_fac i j k := by apply pullback.hom_ext <;> simp
  cocycle i j k := cyclicTripleCocycle f i j k
  f_open _ _ := inferInstance

/-- The glued family maps to its original ambient scheme. -/
def toAmbient : (glueData f).glued ⟶ X :=
  Multicoequalizer.desc (glueData f).toGlueData.diagram X f (by
    rintro ⟨i, j⟩
    change pullback.fst (f i) (f j) ≫ f i =
      ((pullbackSymmetry (f i) (f j)).hom ≫ pullback.fst (f j) (f i)) ≫ f j
    simp only [pullbackSymmetry_hom_comp_fst]
    exact pullback.condition)

/-- The glued ambient map restricts to the original family morphism on every chart. -/
@[reassoc]
theorem ι_toAmbient (i : ι) : (glueData f).ι i ≫ toAmbient f = f i :=
  Multicoequalizer.π_desc (glueData f).toGlueData.diagram X f _ i

end FLT.Mazur.MonoFamilyGluing
