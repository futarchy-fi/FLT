/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankClosedLifts

/-!
# Global closed lifts from independent rank thickenings

Affine all-order lifts glue by monicity on the full coefficient scheme.
The coefficient scheme only needs to be locally Noetherian: neither affine
nor quasi-compact is required. The construction uses ordinary open gluing,
not descent along the nonflat rank stages.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Z Y : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom]
  (x y : B ⟶ S) [IsLocallyNoetherian B]

/-- Local coefficient detection constructs an isomorphism of the entire closed comparison. -/
theorem closedImmersion_isIso_of_doubleRank_global (c : Z ⟶ B) [IsClosedImmersion c]
    (h : ∀ n m r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s) : IsIso c := by
  have hl : ∀ i : B.affineCover.I₀, ∃ d : B.affineCover.X i ⟶ Z,
      d ≫ c = B.affineCover.f i := by
    intro i
    let _ := isLocallyNoetherian_of_isOpenImmersion (B.affineCover.f i)
    exact (existsUnique_test_lift_of_doubleRank E x y (B.affineCover.f i) c h).exists
  choose d hd using hl
  have hc : ∀ i j, pullback.fst (B.affineCover.f i) (B.affineCover.f j) ≫ d i =
      pullback.snd (B.affineCover.f i) (B.affineCover.f j) ≫ d j := by
    intro i j
    apply (cancel_mono c).mp
    rw [Category.assoc, Category.assoc, hd, hd, pullback.condition]
  let g : B ⟶ Z := B.affineCover.glueMorphisms d hc
  have hg : g ≫ c = 𝟙 B := by
    apply B.affineCover.hom_ext
    intro i
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hd, Category.comp_id]
  refine ⟨g, ?_, hg⟩
  apply (cancel_mono c).mp
  rw [Category.assoc, hg, Category.comp_id, Category.id_comp]

/-- All independent rank arrows yield a unique original arrow on any locally Noetherian test. -/
theorem existsUnique_global_lift_of_doubleRank (c : Z ⟶ Y) [Mono c] (t : B ⟶ Y)
    [IsClosedImmersion (pullback.snd c t)]
    (h : ∀ n m r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s ≫ t) :
    ∃! d : B ⟶ Z, d ≫ c = t := by
  let _ : IsIso (pullback.snd c t) :=
    closedImmersion_isIso_of_doubleRank_global E x y (pullback.snd c t) (by
      intro n m r s
      obtain ⟨d, hd⟩ := h n m r s
      exact ⟨pullback.lift d (doubleRankMap E x y n m r s) hd,
        pullback.lift_snd _ _ _⟩)
  refine ⟨inv (pullback.snd c t) ≫ pullback.fst c t, ?_, ?_⟩
  · change (inv (pullback.snd c t) ≫ pullback.fst c t) ≫ c = t
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · intro d hd
    apply (cancel_mono c).mp
    rw [hd, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end FLT.Mazur.RelativeOrderedTuples
