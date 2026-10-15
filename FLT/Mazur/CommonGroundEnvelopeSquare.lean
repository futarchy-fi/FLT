/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianNormFullFiber

/-!
# The full independent envelope over a common scheme ground

Both source and translation are actual pullbacks along the same ground map.
The comparison retains their full product, including all independent residual
coordinates. No affine presentation of the new ground is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CommonGroundEnvelope
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S U : Scheme.{u}} (q : U ⟶ S)

/-- The whole pullback, viewed over the new ground. -/
def changed (A : Over S) : Over U := Over.mk (pullback.snd A.hom q)

variable (A V : Over S)
local notation "B" => changed q A
local notation "W" => changed q V
local notation "π" => Over.Hom.left (prod.fst : prod B W ⟶ B)
local notation "ρ" => Over.Hom.left (prod.snd : prod B W ⟶ W)
local notation "π₀" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "ρ₀" => Over.Hom.left (prod.snd : prod A V ⟶ V)

/-- Comparison to the original envelope using both actual pullback projections. -/
def comparison : (prod B W).left ⟶ (prod A V).left :=
  (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip.lift
    (ρ ≫ pullback.fst V.hom q) (π ≫ pullback.fst A.hom q) (by
      simp only [Category.assoc, pullback.condition]
      exact congrArg (fun h ↦ h ≫ q)
        ((prod.snd : prod B W ⟶ W).w.trans (prod.fst : prod B W ⟶ B).w.symm))

/-- The original source coordinate is unchanged. -/
@[reassoc] theorem comparison_fst :
    comparison q A V ≫ π₀ = π ≫ pullback.fst A.hom q :=
  IsPullback.lift_snd _ _ _ _

/-- The original independent translation coordinate is unchanged. -/
@[reassoc] theorem comparison_snd :
    comparison q A V ≫ ρ₀ = ρ ≫ pullback.fst V.hom q :=
  IsPullback.lift_fst _ _ _ _

/-- This is the full Cartesian envelope square, not merely a finite core square. -/
theorem isPullback :
    IsPullback (comparison q A V) π π₀ (pullback.fst A.hom q) := by
  have hB := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B W)).flip
  have hA := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
  have hs := hB.paste_horiz (IsPullback.of_hasPullback V.hom q)
  simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at hs hA
  change IsPullback (ρ ≫ pullback.fst V.hom q) π V.hom
    (pullback.snd A.hom q ≫ q) at hs
  rw [← pullback.condition, ← comparison_snd q A V] at hs
  exact hs.of_right (comparison_fst q A V) hA

/-- Every independent original fiber point is tested by the changed envelope. -/
theorem fullFiberLocus (O : (prod A V).left.Opens) :
    SchemeOpenEnvelope.fullFiberLocus π (comparison q A V ⁻¹ᵁ O) =
      pullback.fst A.hom q ⁻¹' SchemeOpenEnvelope.fullFiberLocus π₀ O :=
  SchemeOpenEnvelope.fullFiberLocus_baseChange (isPullback q A V) O

/-- An etale common ground retains the original maximal open full-fiber domain. -/
theorem fullFiberInterior [Etale q] (O : (prod A V).left.Opens) :
    SchemeOpenEnvelope.fullFiberInterior π (comparison q A V ⁻¹ᵁ O) =
      pullback.fst A.hom q ⁻¹ᵁ SchemeOpenEnvelope.fullFiberInterior π₀ O :=
  SchemeOpenEnvelope.fullFiberInterior_baseChange (isPullback q A V) O
    (pullback.fst A.hom q).isOpenMap

end FLT.Mazur.CommonGroundEnvelope
