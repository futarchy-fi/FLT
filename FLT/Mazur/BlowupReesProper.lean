/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesContraction
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Properness of the actual Rees contraction

A finitely generated center gives a finite type Rees algebra over its
proved degree-zero ring. Projective-spectrum properness then applies to
the actual contraction to the original affine base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- A finite center gives a finite type Rees algebra over its original ring. -/
theorem finiteType_of_fg (hI : I.FG) : Algebra.FiniteType A (reesAlgebra I) :=
  ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩

/-- Finite generation also holds over the actual degree-zero Rees component. -/
theorem finiteType_zero_of_fg (hI : I.FG) :
    Algebra.FiniteType (component I 0) (reesAlgebra I) := by
  obtain ⟨S, hS⟩ := (finiteType_of_fg I hI).out
  refine ⟨⟨S, top_unique ?_⟩⟩
  intro z hzTop
  clear hzTop
  have hz : z ∈ Algebra.adjoin A (S : Set (reesAlgebra I)) := by
    rw [hS]
    trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap a =>
    change algebraMap (component I 0) (reesAlgebra I) (originalToZero I a) ∈ _
    exact Subalgebra.algebraMap_mem _ _
  | add a b ha hb ih ih' => exact Subalgebra.add_mem _ ih ih'
  | mul a b ha hb ih ih' => exact Subalgebra.mul_mem _ ih ih'

/-- The canonical contraction of the finitely generated Rees center is proper. -/
theorem contraction_isProper (hI : I.FG) : IsProper (contraction I) := by
  let _ := finiteType_zero_of_fg I hI
  let e := RingEquiv.toCommRingCatIso (R := A) (S := component I 0) (originalZeroEquiv I)
  change IsProper (Proj.toSpecZero (component I) ≫ Spec.map e.hom)
  infer_instance

end FLT.Mazur.BlowupRees
