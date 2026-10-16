/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankInterior
public import FLT.Mazur.RelativeFrameRankImage
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts

/-!
# Actual complete-interior coverage of original rank strata

The original open where n-frames exist and larger frames cannot approach is
covered by complete normalized interiors. The lifts use the whole original
relation and its identity arrow, with no discarded fiber points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur
namespace EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ)
local instance stratumOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stratumOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stratumOver_quasiCompact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
/-- Every point of the actual rank stratum has a complete interior normalized lift. -/
theorem exists_rankStratum_interior_lift (x : A)
    (hx : x ∈ rankStratumOpen (Over.mk p) n) :
    ∃ (o : Fin n) (y : source p q (Fin n) o),
      first p q (Fin n) o y = x ∧
      y ∈ completeInterior (p := p) (q := q) (Fin n) o := by
  obtain ⟨z, hz⟩ := hx.1
  let F := (distinctScheme (Over.mk p) (Fin n)).left
  let u := F.fromSpecResidueField z
  let b := u ≫ (distinctScheme (Over.mk p) (Fin n)).hom
  let t : Over.mk b ⟶ distinctScheme (Over.mk p) (Fin n) := Over.homMk u
  have hu : u default = z := Scheme.fromSpecResidueField_apply z default
  have hb : b default = x := by
    change (distinctScheme (Over.mk p) (Fin n)).hom (u default) = x
    rw [hu, hz]
  have ht := geometric_complete_of_rankBound (Over.mk p) n t (hb ▸ hx.2)
  obtain ⟨o, ho⟩ := exists_identity_coordinate e (Fin n) t ht
  have h : b = (t ≫ distinctCoordinate (Over.mk p) (Fin n) o).left ≫ q := by
    rw [ho, Category.assoc, e.reflexivity₂, Category.comp_id]
  let v := lift p q (Fin n) o t h
  have hv : first p q (Fin n) o (v default) = x :=
    (congrArg (fun f ↦ f default) (lift_first p q (Fin n) o t h)).trans hb
  refine ⟨o, v default, hv, mem_completeInterior_of_rankBound n o _ ?_⟩
  rw [hv]
  exact hx.2

end EquivalenceRelationNormalizedFrames
end FLT.Mazur
