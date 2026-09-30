/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistCohomology
public import FLT.Mazur.FiniteAffineCoverDimension

/-! # Positive cohomology vanishing for projective twisting sheaves -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ProjectiveSpace

open LocalizationDegree

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The explicit Cech degree threshold implies vanishing of actual positive cohomology. -/
theorem twist_moduleH_subsingleton [Fintype ι] (d : ℤ)
    (hd : -(Fintype.card ι : ℤ) < d) (q : ℕ) :
    Subsingleton (ModuleH (twistingSheaf R ι d) (q + 1)) := by
  let _zeroHomology := ModuleCat.isZero_iff_subsingleton.mp
    (TwistCechCohomology.sheaf_isZero_homology_large R ι d hd q)
  exact (twistModuleHEquiv R ι d (q + 1)).symm.injective.subsingleton

/-- Nonnegative twists have no positive cohomology, including an empty chart index. -/
theorem twist_moduleH_subsingleton_nonneg [Finite ι] (d : ℤ) (hd : 0 ≤ d) (q : ℕ) :
    Subsingleton (ModuleH (twistingSheaf R ι d) (q + 1)) := by
  let _index : Fintype ι := Fintype.ofFinite ι
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let _empty := h
    exact emptyAffineCover_moduleH_subsingleton (twistingSheaf R ι d) (chart R ι)
      (fun i ↦ Proj.isAffineOpen_basicOpen (grading R ι) (X i)
        (isHomogeneous_X R i) (by decide)) (iSup_chart R ι) (q + 1)
  | inr h =>
    let _nonempty := h
    have hc := Fintype.card_pos (α := ι)
    exact twist_moduleH_subsingleton R ι d (by omega) q

end FLT.Mazur.ProjectiveSpace
