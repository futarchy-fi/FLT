/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameExactRank

/-!
# Original frame ranks under arbitrary base change

The full geometric section types before and after pullback are equivalent.
Complete frames therefore have the same length. This transports every rank
image and exact rank without flatness or reduction of the coefficient scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) (b : B ⟶ S)

/-- Base change retains every original section over a fixed coefficient map. -/
def pullbackSectionEquiv {T : Scheme.{0}} (a : T ⟶ B) :
    (Over.mk a ⟶ Over.mk (pullback.snd E.hom b)) ≃ (Over.mk (a ≫ b) ⟶ E) where
  toFun r := Over.homMk (r.left ≫ pullback.fst E.hom b) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ b) r.w)
  invFun r := Over.homMk (pullback.lift r.left a r.w) (pullback.lift_snd _ _ _)
  left_inv r := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans r.w.symm
  right_inv r := Over.OverMorphism.ext (pullback.lift_fst _ _ _)

variable [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom]
local instance rankPullback_etale : Etale (Over.mk (pullback.snd E.hom b)).hom :=
  inferInstanceAs (Etale (pullback.snd E.hom b))
local instance rankPullback_separated : IsSeparated (Over.mk (pullback.snd E.hom b)).hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom b))
local instance rankPullback_compact : QuasiCompact (Over.mk (pullback.snd E.hom b)).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd E.hom b))

/-- Complete geometric frames compute the same rank after arbitrary original base change. -/
theorem geometric_rankImage_pullback_iff {K : Type} [Field K] [IsSepClosed K]
    (a : Spec (.of K) ⟶ B) (n : ℕ) :
    a default ∈ rankImageOpen (Over.mk (pullback.snd E.hom b)) n ↔
      (a ≫ b) default ∈ rankImageOpen E n := by
  let F := Over.mk (pullback.snd E.hom b)
  obtain ⟨r, t, ht⟩ := exists_complete_geometric_tuple F a
  obtain ⟨s, u, hu⟩ := exists_complete_geometric_tuple E (a ≫ b)
  let e : Fin r ≃ Fin s := (completeCoordinateEquiv F (Fin r) t ht).trans
    ((pullbackSectionEquiv E b a).trans (completeCoordinateEquiv E (Fin s) u hu).symm)
  have hrs : r = s := Fintype.card_fin r ▸ Fintype.card_fin s ▸ Fintype.card_congr e
  rw [geometric_mem_rankImage_iff F t ht, geometric_mem_rankImage_iff E u hu, hrs]

/-- All original rank images commute with arbitrary base change on actual scheme points. -/
theorem rankImage_pullback_iff (x : B) (n : ℕ) :
    x ∈ rankImageOpen (Over.mk (pullback.snd E.hom b)) n ↔
      b x ∈ rankImageOpen E n := by
  let K := AlgebraicClosure (B.residueField x)
  let a := Spec.map (CommRingCat.ofHom (algebraMap (B.residueField x) K)) ≫
    B.fromSpecResidueField x
  have ha : a default = x := B.fromSpecResidueField_apply x _
  have h := geometric_rankImage_pullback_iff E b a n
  change a default ∈ _ ↔ b (a default) ∈ _ at h
  rwa [ha] at h

/-- The original exact rank is preserved, including on nonreduced coefficient schemes. -/
theorem exactRank_pullback_iff (x : B) (n : ℕ) :
    x ∈ exactRank (Over.mk (pullback.snd E.hom b)) n ↔ b x ∈ exactRank E n :=
  and_congr (rankImage_pullback_iff E b x n)
    (not_congr (rankImage_pullback_iff E b x (n + 1)))

end FLT.Mazur.RelativeOrderedTuples
