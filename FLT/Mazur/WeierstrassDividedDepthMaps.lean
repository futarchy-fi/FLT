/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# Direct contraction between packaged actual depths

The direct depth maps are the already proved coordinate transitions. They
satisfy identity and composition laws, including the exact successor map
used by exterior replacement, and retain the original projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {k l m : ℕ}

/-- The existing actual transition between any two available depths. -/
def depthMap (d : Data W π k) (e : Data W π l) (h : k ≤ l) : chart e ⟶ chart d :=
  WeierstrassDilatation.depthTransitionMorphism π k l hπ h W d.b3 d.b4 d.b6
    e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6

/-- At a fixed depth the coordinate contraction is the identity. -/
@[simp] theorem depthMap_self (d : Data W π k) : depthMap hπ d d le_rfl = 𝟙 _ := by
  unfold depthMap WeierstrassDilatation.depthTransitionMorphism
  rw [WeierstrassDilatation.depthTransition_self]
  exact Scheme.Spec.map_id _

/-- The actual direct depth maps compose. -/
@[reassoc] theorem depthMap_comp (d : Data W π k) (e : Data W π l) (f : Data W π m)
    (h : k ≤ l) (h' : l ≤ m) :
    depthMap hπ e f h' ≫ depthMap hπ d e h = depthMap hπ d f (h.trans h') :=
  WeierstrassDilatation.depthTransitionMorphism_comp π k l m hπ h h' W
    d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 f.b3 f.b4 f.b6
    d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6
    f.factor3 f.factor4 f.factor6

/-- The step used in whole replacement is exactly this direct map for adjacent depths. -/
theorem transition_eq_depthMap (d : Data W π k) (e : Data W π (k + 1)) :
    transition hπ d e = depthMap hπ d e (Nat.le_succ k) := rfl

/-- Every direct depth map retains the original cubic coordinates. -/
@[reassoc] theorem depthMap_toCurve (d : Data W π k) (e : Data W π l) (h : k ≤ l) :
    depthMap hπ d e h ≫ toCurve d = toCurve e :=
  WeierstrassDilatation.depthTransitionMorphism_contraction π k l hπ h W
    d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6
    e.factor3 e.factor4 e.factor6

end FLT.Mazur.WeierstrassDividedDepth
