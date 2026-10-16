/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteInterior
public import FLT.Mazur.RelativeFrameRankOpen

/-!
# Complete normalized interiors over original rank opens

Rank exclusion constructs actual open domains of complete normalized frames.
This discharges interior membership from original base geometry, without
assuming completeness on the desired chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n)
local instance rankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankOver_quasiCompact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- The inverse image of the actual rank bound consists of complete normalized points. -/
theorem first_rankBound_complete :
    (first p q (Fin n) o ⁻¹ᵁ rankBoundOpen (Over.mk p) n : Set _) ⊆
      completePointLocus (p := p) (q := q) (Fin n) o := by
  intro x hx
  rw [completePointLocus_eq_preimage]
  exact rankBound_preimage_complete (Over.mk p) n hx

/-- Rank exclusion puts the entire open preimage inside the intrinsic complete interior. -/
theorem first_rankBound_le_completeInterior :
    first p q (Fin n) o ⁻¹ᵁ rankBoundOpen (Over.mk p) n ≤
      completeInterior (p := p) (q := q) (Fin n) o :=
  le_completeInterior (Fin n) o _ (first_rankBound_complete n o)

/-- A normalized point over the original rank bound has genuine interior completeness. -/
theorem mem_completeInterior_of_rankBound (x : source p q (Fin n) o)
    (hx : first p q (Fin n) o x ∈ rankBoundOpen (Over.mk p) n) :
    x ∈ completeInterior (p := p) (q := q) (Fin n) o :=
  first_rankBound_le_completeInterior n o hx

end FLT.Mazur.EquivalenceRelationNormalizedFrames
