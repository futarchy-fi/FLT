/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowNegativePairCover

/-!
# Shallow pair outputs at a supplied common finite stage

Promote both signs of the three-source cover through the actual smooth-stage
transition. The full original cubic and coefficient morphisms are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hlo : 2 * k < m) (hhi : m < 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hstage : m - 2 * k ≤ j)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "hd" => hstage.trans hj
local notation "old" => finiteGlobalStructure hπ data (m - 2 * k) hd
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "na" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "nc" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 c
local notation "pos" => nodalShallowPositivePairOutput D hlo hhi data hd d a c
local notation "neg" => nodalShallowNegativePairOutput D hlo hhi data hd d a c
local notation "advance" => finiteGlobalSmoothTransition hπ data (m - 2 * k) j hstage hj

/-- Every positive local output reaches the chosen common smooth stage. -/
def nodalShallowPositivePairOutputAt (i : Option Bool) :
    nodalShallowPositivePairSource D hlo hhi data hd d a c i ⟶ (U).toScheme :=
  pos i ≫ advance

/-- Promotion keeps the complete original cubic morphism on each positive source. -/
@[reassoc] theorem nodalShallowPositivePairOutputAt_contraction (i : Option Bool) :
    nodalShallowPositivePairOutputAt D hlo hhi data j hj hstage d a c i ≫
      (U).ι ≫ finiteGlobalContraction hπ data j hj =
    pos i ≫ (old).smoothLocus.ι ≫ finiteGlobalContraction hπ data (m - 2 * k) hd := by
  rw [nodalShallowPositivePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- Positive promoted outputs retain the original coefficient point. -/
@[reassoc] theorem nodalShallowPositivePairOutputAt_structure (i : Option Bool) :
    nodalShallowPositivePairOutputAt D hlo hhi data j hj hstage d a c i ≫ (U).ι ≫ base =
      nodalShallowPositivePairInclusion D hlo hhi data hd d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalShallowPositivePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_structure,
    nodalShallowPositivePairOutput_structure]

/-- Every negative local output reaches the same chosen common smooth stage. -/
def nodalShallowNegativePairOutputAt (i : Option Bool) :
    nodalShallowPositivePairSource D hlo hhi data hd d na nc i ⟶ (U).toScheme :=
  neg i ≫ advance

/-- Promotion keeps the complete original cubic morphism on each negative source. -/
@[reassoc] theorem nodalShallowNegativePairOutputAt_contraction (i : Option Bool) :
    nodalShallowNegativePairOutputAt D hlo hhi data j hj hstage d a c i ≫
      (U).ι ≫ finiteGlobalContraction hπ data j hj =
    neg i ≫ (old).smoothLocus.ι ≫ finiteGlobalContraction hπ data (m - 2 * k) hd := by
  rw [nodalShallowNegativePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- Negative promoted outputs retain the original coefficient point. -/
@[reassoc] theorem nodalShallowNegativePairOutputAt_structure (i : Option Bool) :
    nodalShallowNegativePairOutputAt D hlo hhi data j hj hstage d a c i ≫ (U).ι ≫ base =
      nodalShallowPositivePairInclusion D hlo hhi data hd d na nc i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalShallowNegativePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_structure,
    nodalShallowNegativePairOutput_structure]

end FLT.Mazur.WeierstrassDividedDepth
