/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstOrderAffineFrames
public import FLT.Mazur.PolygonCompletePointOriginChart
public import FLT.Mazur.CartierTensorRatioIdeal

/-!
# The full original marking ideal in normalized projective coordinates

On every Cartier chart inside the actual first-order neighborhood, the original
X/Y ratio generates the original marking ideal, with multiplicity retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "V" => completePointOriginOpen K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- The actual X/Y ratio generates the full marking ideal on each first-order Cartier chart. -/
theorem completePointRatio_span_marking (A : (exactVeroneseProj K n h).affineOpens)
    (hA : A.1 ≤ completePointFirstOrderOpen K n h i) (hC : CartierChart (s).ker A) :
    Ideal.span {(sectionRatioOn (tensorPower (L) 3) (T 1) A.1
      ((hA.trans inf_le_left).trans (completePointOriginOpen_le_y K n h i)) (T 0))} =
        (s).ker.ideal A := by
  change Ideal.span {(sectionRatioOn (tensorPower (L) 3) (completePointProjectiveY K n h i)
    A.1 _ (completePointProjectiveX K n h i))} = _
  rw [completePointProjectiveX_canonicalFactor]
  exact cartierTensorRatio_span_on (s).ker hI A hC 2
    (completePointPoleTwoSection K n h i) (completePointProjectiveY K n h i)
    (hA.trans inf_le_right)
    ((hA.trans inf_le_left).trans (completePointOriginOpen_le_y K n h i))

end FLT.Mazur.PolygonInfinitesimalStages
