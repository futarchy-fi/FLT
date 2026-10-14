/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Full relations under monomorphic target base change

A coequalized relation remains saturated after any monomorphic target base
change, including closed nonreduced subschemes. Its full two-endpoint restriction
is the pullback of either original endpoint. No kernel equality is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {D A B Q T : Scheme.{u}} (p q : D ⟶ A) (v : A ⟶ Q)
  (i : T ⟶ Q) (u : B ⟶ A) (w : B ⟶ T)
  (h : IsPullback u w v i) (he : p ≫ v = q ≫ v)

/-- The second endpoint lifts with the same new target coordinate as the first. -/
def monicBaseSecond : pullback p u ⟶ B :=
  h.lift (pullback.fst p u ≫ q) (pullback.snd p u ≫ w) (by
    rw [Category.assoc, ← he, ← Category.assoc, pullback.condition,
      Category.assoc, h.w, ← Category.assoc])

@[reassoc]
theorem monicBaseSecond_source : monicBaseSecond p q v i u w h he ≫ u =
    pullback.fst p u ≫ q := h.lift_fst _ _ _

@[reassoc]
theorem monicBaseSecond_target : monicBaseSecond p q v i u w h he ≫ w =
    pullback.snd p u ≫ w := h.lift_snd _ _ _

/-- All arrows over one lifted endpoint retain their complete second endpoint. -/
def monicBaseFromFirst : pullback p u ⟶ doubleDomain p q u :=
  lift p q u (pullback.fst p u) (pullback.snd p u)
    (monicBaseSecond p q v i u w h he) pullback.condition
    (monicBaseSecond_source p q v i u w h he).symm

variable [Mono i]

/-- The full double restriction is exactly a single original endpoint base change. -/
def monicBaseFirstIso : doubleDomain p q u ≅ pullback p u where
  hom := pullback.fst (pullback.fst p u ≫ q) u
  inv := monicBaseFromFirst p q v i u w h he
  hom_inv_id := by
    let _ := h.mono_fst_of_mono
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [monicBaseFromFirst, lift, Category.assoc, pullback.lift_fst,
          Category.id_comp]
      · simp only [monicBaseFromFirst, lift, Category.assoc, pullback.lift_fst,
          pullback.lift_snd, Category.id_comp]
    · apply (cancel_mono u).mp
      simp only [Category.assoc, monicBaseFromFirst, lift, pullback.lift_snd,
        monicBaseSecond_source, Category.id_comp]
      exact pullback.condition
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [monicBaseFromFirst, lift, pullback.lift_fst,
        Category.id_comp]
    · simp only [monicBaseFromFirst, lift, pullback.lift_fst,
        pullback.lift_snd, Category.id_comp]

include h he

/-- The first endpoint square retains the entire original relation scheme. -/
theorem monicBase_fst_isPullback : IsPullback (arrow p q u) (fst p q u) p u :=
  IsPullback.of_iso_pullback ⟨arrow_fst p q u⟩
    (monicBaseFirstIso p q v i u w h he) rfl rfl

/-- Both endpoints have the same actual new target coordinate, even on nonreduced tests. -/
@[reassoc]
theorem monicBase_condition : fst p q u ≫ w = snd p q u ≫ w := by
  apply (cancel_mono i).mp
  rw [Category.assoc, Category.assoc, ← h.w, ← Category.assoc,
    ← Category.assoc, ← arrow_fst, ← arrow_snd, Category.assoc, Category.assoc, he]

/-- The second endpoint square is also an actual base change, not a smaller relation. -/
theorem monicBase_snd_isPullback : IsPullback (arrow p q u) (snd p q u) q u := by
  have hp := (monicBase_fst_isPullback p q v i u w h he).paste_vert h
  rw [he, monicBase_condition p q v i u w h he] at hp
  exact hp.of_bot (arrow_snd p q u) h

end FLT.Mazur.SchemeRelationRestriction
