/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteExactRank
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts
public import FLT.Mazur.EquivalenceRelationNormalizedSubframe

/-!
# Normalized covers of the full exact rank locus

Every point of the closed-boundary exact rank locus lifts to normalized frames
with a prescribed distinguished label. Pullback gives an etale surjection on
any scheme supported on that locus, preserving all nilpotent structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ) (o : Fin n)
local instance exactCoverOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance exactCoverOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance exactCoverOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] source

include e in
/-- A prescribed normalized label covers every point of the full exact rank locus. -/
theorem exactRank_mem_range_first (x : A) (hx : x ∈ exactRank (Over.mk p) n) :
    x ∈ Set.range (first p q (Fin n) o) := by
  obtain ⟨z, hz⟩ := hx.1
  let F := (distinctScheme (Over.mk p) (Fin n)).left
  let u := F.fromSpecResidueField z
  let b := u ≫ (distinctScheme (Over.mk p) (Fin n)).hom
  let t : Over.mk b ⟶ distinctScheme (Over.mk p) (Fin n) := Over.homMk u
  have hb : b default = x := by
    change (distinctScheme (Over.mk p) (Fin n)).hom (u default) = x
    rw [Scheme.fromSpecResidueField_apply, hz]
  have ht := geometric_complete_of_rankAtMost (Over.mk p) n t (hb ▸ hx.2)
  obtain ⟨j, hj⟩ := exists_identity_coordinate e (Fin n) t ht
  have h : b = (t ≫ distinctCoordinate (Over.mk p) (Fin n) j).left ≫ q := by
    rw [hj, Category.assoc, e.reflexivity₂, Category.comp_id]
  let v := lift p q (Fin n) j t h
  let w := v ≫ subframeMap e j o (Equiv.swap o j).toEmbedding
  refine ⟨w default, ?_⟩
  have hw : w ≫ first p q (Fin n) o = b := by
    dsimp only [w]
    rw [Category.assoc, subframeMap_first]
    simp only [Equiv.toEmbedding_apply, Equiv.swap_apply_left]
    rw [← first_eq_distinguished, lift_first]
  exact (congrArg (fun f ↦ f default) hw).trans hb

variable {B : Scheme.{0}} (b : B ⟶ A)

/-- Pull back the entire normalized source to the unchanged coefficient scheme. -/
def exactNormalizedCover : Scheme := pullback (first p q (Fin n) o) b

/-- The coefficient projection of the actual normalized pullback. -/
def exactNormalizedProjection : exactNormalizedCover (p := p) (q := q) n o b ⟶ B :=
  pullback.snd (first p q (Fin n) o) b

/-- The tautological normalized frame on this cover. -/
def exactNormalizedFrame : exactNormalizedCover (p := p) (q := q) n o b ⟶ source p q (Fin n) o :=
  pullback.fst (first p q (Fin n) o) b

omit [Etale p] [QuasiCompact p] in
/-- The frame retains its prescribed original endpoint as an exact scheme morphism. -/
@[reassoc] theorem exactNormalizedFrame_first :
    exactNormalizedFrame (p := p) (q := q) n o b ≫ first p q (Fin n) o =
      exactNormalizedProjection (p := p) (q := q) n o b ≫ b := pullback.condition

include e in
omit [QuasiCompact p] in
/-- The constructed cover is etale, including over arbitrary nonreduced coefficients. -/
theorem exactNormalizedProjection_etale :
    Etale (exactNormalizedProjection (p := p) (q := q) n o b) := by
  let _ := first_etale e (Fin n) o
  exact inferInstanceAs (Etale (pullback.snd (first p q (Fin n) o) b))

include e in
/-- Exact rank gives surjectivity on the entire coefficient scheme, including residual points. -/
theorem exactNormalizedProjection_surjective (hb : Set.range b ⊆ exactRank (Over.mk p) n) :
    Function.Surjective (exactNormalizedProjection (p := p) (q := q) n o b) := by
  intro x
  change x ∈ Set.range (pullback.snd (first p q (Fin n) o) b)
  rw [Scheme.Pullback.range_snd]
  exact exactRank_mem_range_first e n o (b x) (hb (Set.mem_range_self x))

/-- Every cover point is complete; no open-interior rank condition is needed. -/
theorem exactNormalizedFrame_complete (hb : Set.range b ⊆ rankAtMost (Over.mk p) n)
    (x : exactNormalizedCover (p := p) (q := q) n o b) :
    exactNormalizedFrame (p := p) (q := q) n o b x ∈
      completePointLocus (p := p) (q := q) (Fin n) o := by
  rw [completePointLocus_eq_rankAtMost_preimage]
  change (exactNormalizedFrame (p := p) (q := q) n o b ≫ first p q (Fin n) o) x ∈
    rankAtMost (Over.mk p) n
  rw [exactNormalizedFrame_first]
  exact hb (Set.mem_range_self _)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
