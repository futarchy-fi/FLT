/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionUnitCocycle
public import FLT.Mazur.ModuleUnitCocyclePullback
public import FLT.Mazur.ModuleUnitCocycleCongr

/-!
# Pullback recovery from descended intersection units

Recovery of the pair units identifies the actual pullback of the glued line
sheaf with the original cocycle sheaf. All smaller-open identities follow
from the genuine restriction laws.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {X Y : Scheme.{u}} {ι : Type u} (O : NonemptyChartSet ι → Y.Opens)
  (hanti : Antitone O) (hunion : ∀ s t, O (unionChartSet s t) = O s ⊓ O t)
  (y : ∀ s, IntersectionPair s → Γ(Y, O s)ˣ)
  (hnat : ∀ {s t} (h : s ≤ t) (k : IntersectionPair s),
    res (hanti h) (y s k : Γ(Y, O s)) =
      (y t (intersectionPairMap (homOfLE h) k) : Γ(Y, O t)))
  (hmul : ∀ s (k : IntersectionTriple s),
    y s (k.1, k.2.1) * y s (k.2.1, k.2.2) = y s (k.1, k.2.2))

/-- The intersection cocycle uses exactly the prescribed unit on the pair intersection. -/
theorem intersectionUnitsCocycle_pair (i j : ι) :
    (intersectionUnitsCocycle O hanti hunion y hnat hmul).unit i j (O (pairChartSet i j))
      (by rw [pairChartSet, hunion]; exact inf_le_left)
      (by rw [pairChartSet, hunion]; exact inf_le_right) =
        y (pairChartSet i j) (⟨i, by simp⟩, ⟨j, by simp⟩) := by
  apply Units.ext
  exact res_self _ _

variable (f : X ⟶ Y) {U : ι → X.Opens} (g : Cocycle U)
  (hU : ∀ i, f ⁻¹ᵁ O (singletonChartSet i) = U i)
  (hrec : ∀ i j, Units.map (f.app (O (pairChartSet i j))).hom.toMonoidHom
    (y (pairChartSet i j) (⟨i, by simp⟩, ⟨j, by simp⟩)) =
      g.unit i j (f ⁻¹ᵁ O (pairChartSet i j))
        ((f.preimage_mono (by rw [pairChartSet, hunion]; exact inf_le_left)).trans (hU i).le)
        ((f.preimage_mono (by rw [pairChartSet, hunion]; exact inf_le_right)).trans (hU j).le))

include hrec in
/-- Pair recovery determines the inverse-image cocycle on every common subopen. -/
theorem intersectionUnitsCocycle_inverseImage_unit (i j : ι) (V : X.Opens)
    (hi : V ≤ f ⁻¹ᵁ O (singletonChartSet i))
    (hj : V ≤ f ⁻¹ᵁ O (singletonChartSet j)) :
    ((intersectionUnitsCocycle O hanti hunion y hnat hmul).inverseImage f).unit
      i j V hi hj = g.unit i j V (hi.trans (hU i).le) (hj.trans (hU j).le) := by
  have hV : V ≤ f ⁻¹ᵁ O (pairChartSet i j) := by
    rw [pairChartSet, hunion, f.preimage_inf]
    exact le_inf hi hj
  apply Units.ext
  change ((intersectionUnitsCocycle O hanti hunion y hnat hmul).inverseImageUnit
    f i j V hi hj : Γ(X, V)) = _
  rw [Cocycle.inverseImageUnit_eq _ f i j V hi hj (O (pairChartSet i j))
    (by rw [pairChartSet, hunion]; exact inf_le_left)
    (by rw [pairChartSet, hunion]; exact inf_le_right) hV,
    intersectionUnitsCocycle_pair]
  change res hV (f.app _ (y (pairChartSet i j)
    (⟨i, by simp⟩, ⟨j, by simp⟩)).val) = _
  rw [show f.app _ (y (pairChartSet i j)
    (⟨i, by simp⟩, ⟨j, by simp⟩)).val = _ from congrArg Units.val (hrec i j)]
  exact g.natural _ _ _ _ _

/-- The sheaf glued from descended units pulls back to the prescribed cocycle sheaf. -/
def intersectionUnitsCocyclePullbackIso (hcover : (⨆ i, O (singletonChartSet i)) = ⊤) :
    (Scheme.Modules.pullback f).obj
      (intersectionUnitsCocycle O hanti hunion y hnat hmul).sheaf ≅ g.sheaf :=
  (intersectionUnitsCocycle O hanti hunion y hnat hmul).pullbackIso f hcover ≪≫
    Cocycle.sheafIsoOfUnits _ g hU
      (intersectionUnitsCocycle_inverseImage_unit O hanti hunion y hnat hmul f g hU hrec)

end FLT.Mazur.Approximation
