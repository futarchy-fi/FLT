/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalTripleNegativePairCover

/-!
# Triple pair outputs at a supplied common finite stage

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
  {W : WeierstrassCurve R} {π : R} {n k : ℕ} (D : SplitNodeDepth W π (3 * k))
  (hk : 0 < k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (j : ℕ) (hj : j ≤ n) (hstage : k ≤ j)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "hd" => hstage.trans hj
local notation "old" => finiteGlobalStructure hπ data (k) hd
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "na" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "nc" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 c
local notation "pos" => nodalTriplePositivePairOutput D hk data hd d a c
local notation "neg" => nodalTripleNegativePairOutput D hk data hd d a c
local notation "advance" => finiteGlobalSmoothTransition hπ data (k) j hstage hj

/-- Every positive local output reaches the chosen common smooth stage. -/
def nodalTriplePositivePairOutputAt (i : Option Bool) :
    nodalTriplePositivePairSource D hk data hd d a c i ⟶ (U).toScheme :=
  pos i ≫ advance

/-- Promotion keeps the complete original cubic morphism on each positive source. -/
@[reassoc] theorem nodalTriplePositivePairOutputAt_contraction (i : Option Bool) :
    nodalTriplePositivePairOutputAt D hk data j hj hstage d a c i ≫
      (U).ι ≫ finiteGlobalContraction hπ data j hj =
    pos i ≫ (old).smoothLocus.ι ≫ finiteGlobalContraction hπ data (k) hd := by
  rw [nodalTriplePositivePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- Positive promoted outputs retain the original coefficient point. -/
@[reassoc] theorem nodalTriplePositivePairOutputAt_structure (i : Option Bool) :
    nodalTriplePositivePairOutputAt D hk data j hj hstage d a c i ≫ (U).ι ≫ base =
      nodalTriplePositivePairInclusion D hk data hd d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalTriplePositivePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_structure,
    nodalTriplePositivePairOutput_structure]

/-- Every negative local output reaches the same chosen common smooth stage. -/
def nodalTripleNegativePairOutputAt (i : Option Bool) :
    nodalTriplePositivePairSource D hk data hd d na nc i ⟶ (U).toScheme :=
  neg i ≫ advance

/-- Promotion keeps the complete original cubic morphism on each negative source. -/
@[reassoc] theorem nodalTripleNegativePairOutputAt_contraction (i : Option Bool) :
    nodalTripleNegativePairOutputAt D hk data j hj hstage d a c i ≫
      (U).ι ≫ finiteGlobalContraction hπ data j hj =
    neg i ≫ (old).smoothLocus.ι ≫ finiteGlobalContraction hπ data (k) hd := by
  rw [nodalTripleNegativePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_contraction]

/-- Negative promoted outputs retain the original coefficient point. -/
@[reassoc] theorem nodalTripleNegativePairOutputAt_structure (i : Option Bool) :
    nodalTripleNegativePairOutputAt D hk data j hj hstage d a c i ≫ (U).ι ≫ base =
      nodalTriplePositivePairInclusion D hk data hd d na nc i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalTripleNegativePairOutputAt, Category.assoc, finiteGlobalSmoothTransition_structure,
    nodalTripleNegativePairOutput_structure]

end FLT.Mazur.WeierstrassDividedDepth
