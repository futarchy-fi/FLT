/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationExactRankNormalizedCover
public import FLT.Mazur.RelativeDoubleRankThickenings

/-!
# Positive original ranks on every two-endpoint stage

The original identity arrow supplies a distinguished label in any exact-rank
fiber. Thus the independent stages covering scalar pairs always have the
nonempty label sets required for their normalized affine chart constructions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
local instance positiveRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance positiveRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance positiveRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
/-- The identity arrow prevents exact rank zero at every original point. -/
theorem exactRank_nonempty_labels (n : ℕ) (x : A) (hx : x ∈ exactRank (Over.mk p) n) :
    Nonempty (Fin n) := by
  obtain ⟨z, hz⟩ := hx.1
  let F := (distinctScheme (Over.mk p) (Fin n)).left
  let u := F.fromSpecResidueField z
  let b := u ≫ (distinctScheme (Over.mk p) (Fin n)).hom
  let t : Over.mk b ⟶ distinctScheme (Over.mk p) (Fin n) := Over.homMk u
  have hb : b default = x := by
    change (distinctScheme (Over.mk p) (Fin n)).hom (u default) = x
    rw [Scheme.fromSpecResidueField_apply, hz]
  have ht := geometric_complete_of_rankAtMost (Over.mk p) n t (hb ▸ hx.2)
  obtain ⟨o, _⟩ := exists_identity_coordinate e (Fin n) t ht
  exact ⟨o⟩

include e in
/-- Every point of an independent rank stage supplies both actual normalized labels. -/
theorem doubleRank_nonempty_labels (x y : B ⟶ A) (n m r s : ℕ)
    (z : doubleRankThickening (Over.mk p) x y n m r s) :
    Nonempty (Fin n) ∧ Nonempty (Fin m) := by
  obtain ⟨hx, hy⟩ := doubleRankMap_endpoints (Over.mk p) x y n m r s z
  exact ⟨exactRank_nonempty_labels e n _ hx, exactRank_nonempty_labels e m _ hy⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
