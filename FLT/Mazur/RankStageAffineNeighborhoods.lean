/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankThickening
public import FLT.Mazur.FiniteRelationLocallyClosedAffineBasis

/-!
# Invariant affine neighborhoods covering every original infinitesimal rank stage

The finite whole-relation projection and the actual locally closed embedding
construct invariant affine refinements. Every original point lifts to such a
neighborhood at every infinitesimal order, including outside the finite locus.
These locally closed stages are not asserted to be flat over the original source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance rankAffineOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankAffineOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankAffineOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n k : ℕ)
local notation "T" => rankThickening (Over.mk p) n k
local notation "r" => rankStageFirst (p := p) n k
local notation "s" => rankStageSecond e n k

/-- Every invariant open on the full rank stage has invariant affine refinements. -/
theorem exists_rankStage_invariant_affine (W : (rankThickening (Over.mk p) n k).Opens)
    (hW : r ⁻¹ᵁ W = s ⁻¹ᵁ W) (x : T) (hx : x ∈ W) :
    ∃ U : (T).Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧ r ⁻¹ᵁ U = s ⁻¹ᵁ U := by
  let _ := rankStageFirst_finite (p := p) n k
  exact FiniteRelationLocallyClosedAffineBasis.exists_invariant_affine_refinement
    (rankStageEquivalence e n k)
    (rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι
    (rankImageOpen (Over.mk p) n).ι W hW x hx

/-- Every original source point lifts to an affine invariant neighborhood on a full rank stage. -/
theorem exists_rankStage_affine_lift (x : A) :
    ∃ (m : ℕ) (y : rankThickening (Over.mk p) m k)
      (U : (rankThickening (Over.mk p) m k).Opens),
      rankThickeningMap (Over.mk p) m k y = x ∧ IsAffineOpen U ∧ y ∈ U ∧
      rankStageFirst (p := p) m k ⁻¹ᵁ U = rankStageSecond e m k ⁻¹ᵁ U := by
  obtain ⟨m, y, hy⟩ := exists_rankThickening_lift (Over.mk p) x k
  obtain ⟨U, ha, hyU, _, hU⟩ := exists_rankStage_invariant_affine e m k ⊤ (by simp) y trivial
  exact ⟨m, y, U, hy, ha, hyU, hU⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
