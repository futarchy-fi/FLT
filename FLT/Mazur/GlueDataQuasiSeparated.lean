/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasi-separatedness from compact gluing overlaps

Affine charts with compact pairwise gluing schemes give a quasi-separated
scheme. The overlap pullback identifies the actual chart intersections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u

/-- Compact gluing overlaps make the intersections of chart images compact. -/
theorem glueData_isCompact_inter (D : Scheme.GlueData.{u})
    [∀ p, CompactSpace (D.V p)] (i j : D.J) :
    IsCompact (Set.range (D.ι i) ∩ Set.range (D.ι j)) := by
  let h : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
    ⟨⟨(D.glue_condition i j).symm⟩, ⟨D.vPullbackConeIsLimit i j⟩⟩
  let _ : CompactSpace (pullback (C := Scheme) (D.ι i) (D.ι j)) :=
    h.isoPullback.schemeIsoToHomeo.compactSpace
  rw [← IsOpenImmersion.range_pullback_to_base_of_left]
  exact isCompact_range (pullback.fst (D.ι i) (D.ι j) ≫ D.ι i).continuous

/-- Affine gluing charts with compact overlaps yield a quasi-separated scheme. -/
theorem glueData_quasiSeparatedSpace (D : Scheme.GlueData.{u})
    [∀ i, IsAffine (D.U i)] [∀ p, CompactSpace (D.V p)] :
    QuasiSeparatedSpace D.glued := by
  apply Scheme.quasiSeparatedSpace_of_isOpenCover
    (fun i ↦ (D.ι i).opensRange) D.openCover.isOpenCover_opensRange
  · intro i
    exact isAffineOpen_opensRange (D.ι i)
  · exact glueData_isCompact_inter D

end FLT.Mazur
