/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTestDetection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed comparison lifts from all independent rank orders

All-order coefficient detection kills the ideal of a closed comparison.
It constructs a unique arrow on the entire affine Noetherian test, although
the rank stages are not a flat cover. No compatibility choices between the
stage arrows are required, since the comparison is a monomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Z Y : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom]
  (x y : B ⟶ S) [IsAffine B] [IsLocallyNoetherian B]

/-- Independent infinitesimal rank sections kill every equation of a closed immersion. -/
theorem closedImmersion_isIso_of_doubleRank_lifts (c : Z ⟶ B) [IsClosedImmersion c]
    (h : ∀ n m r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s) : IsIso c := by
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  intro a b hab
  apply (section_eq_iff_doubleRank_stages E x y a b).mpr
  intro n m r s
  obtain ⟨d, hd⟩ := h n m r s
  rw [← hd, Scheme.Hom.comp_appTop]
  exact congrArg (fun v ↦ d.appTop v) hab

/-- A closed comparison has a unique full coefficient arrow from its all-order rank arrows. -/
theorem existsUnique_lift_of_doubleRank (c : Z ⟶ Y) [Mono c] (t : B ⟶ Y)
    [IsClosedImmersion (pullback.snd c t)]
    (h : ∀ n m r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s ≫ t) :
    ∃! d : B ⟶ Z, d ≫ c = t := by
  let _ : IsIso (pullback.snd c t) :=
    closedImmersion_isIso_of_doubleRank_lifts E x y (pullback.snd c t) (by
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

omit [IsAffine B] [IsLocallyNoetherian B] in
/-- Stage arrows on the original target also suffice on every affine Noetherian test. -/
theorem existsUnique_test_lift_of_doubleRank {T : Scheme.{0}}
    [IsAffine T] [IsLocallyNoetherian T] (v : T ⟶ B)
    (c : Z ⟶ B) [Mono c] [IsClosedImmersion (pullback.snd c v)]
    (h : ∀ n m r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n m r s) :
    ∃! d : T ⟶ Z, d ≫ c = v := by
  apply existsUnique_lift_of_doubleRank E (v ≫ x) (v ≫ y) c v
  intro n m r s
  obtain ⟨d, hd⟩ := h n m r s
  refine ⟨doubleRankTestMap E x y v n m r s ≫ d, ?_⟩
  rw [Category.assoc, hd, doubleRankTestMap_projection]

end FLT.Mazur.RelativeOrderedTuples
