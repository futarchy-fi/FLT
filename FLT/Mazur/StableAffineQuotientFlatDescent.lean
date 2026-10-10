/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientFlatLocalDescent

/-!
# Global arbitrary-target descent after flat quotient base change

The constructed local descents agree on actual scheme overlaps, by global
cancellation after a further open base change. They therefore glue on the new
base. This proves stability of the categorical quotient under arbitrary flat
base change, including nonaffine and nonseparated new bases.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X S : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (hcover : ⨆ U : Chart ρ, U.val = ⊤)
variable (f : S ⟶ glued ρ) [Flat f]
variable {Y : Scheme.{u}} (k : pullback (map ρ hcover) f ⟶ Y)
variable (hk : ∀ g : G, (FiniteGroupPullback.action ρ _ (map_invariant ρ hcover) f g).hom ≫
  k = k)

/-- The constructed local descents agree on the actual scheme overlap of two base charts. -/
lemma flatLocalDesc_compatible (c d : BaseChart ρ f) :
    pullback.fst c.val.2.val.ι d.val.2.val.ι ≫ flatLocalDesc ρ hcover f k hk c =
      pullback.snd c.val.2.val.ι d.val.2.val.ι ≫ flatLocalDesc ρ hcover f k hk d := by
  let j := pullback.fst c.val.2.val.ι d.val.2.val.ι ≫ c.val.2.val.ι
  let t := FiniteGroupPullback.baseChangeMap (map ρ hcover) f j
  let p := pullback.snd (map ρ hcover) (j ≫ f)
  have hc : t ≫ pullback.snd (map ρ hcover) f =
      (p ≫ pullback.fst c.val.2.val.ι d.val.2.val.ι) ≫ c.val.2.val.ι := by
    exact (FiniteGroupPullback.baseChangeMap_snd _ _ _).trans
      (Category.assoc p _ _).symm
  have hd : t ≫ pullback.snd (map ρ hcover) f =
      (p ≫ pullback.snd c.val.2.val.ι d.val.2.val.ι) ≫ d.val.2.val.ι := by
    exact (FiniteGroupPullback.baseChangeMap_snd _ _ _).trans
      ((congrArg (fun v ↦ p ≫ v)
        (pullback.condition (f := c.val.2.val.ι) (g := d.val.2.val.ι))).trans
        (Category.assoc p _ _).symm)
  have ec : p ≫ pullback.fst c.val.2.val.ι d.val.2.val.ι ≫
      flatLocalDesc ρ hcover f k hk c = t ≫ k := by
    have he := congrArg (fun v ↦ v ≫ flatLocalDesc ρ hcover f k hk c)
      ((sourceChart_isPullback ρ hcover f c).lift_snd t _ hc)
    simpa only [Category.assoc, flatLocalDesc_fac, IsPullback.lift_fst_assoc] using he.symm
  have ed : p ≫ pullback.snd c.val.2.val.ι d.val.2.val.ι ≫
      flatLocalDesc ρ hcover f k hk d = t ≫ k := by
    have he := congrArg (fun v ↦ v ≫ flatLocalDesc ρ hcover f k hk d)
      ((sourceChart_isPullback ρ hcover f d).lift_snd t _ hd)
    simpa only [Category.assoc, flatLocalDesc_fac, IsPullback.lift_fst_assoc] using he.symm
  exact (cancel_epi p).mp (ec.trans ed.symm)

/-- The actual descended morphism on an arbitrary flat new base. -/
def flatDesc : S ⟶ Y :=
  (baseCover ρ f).glueMorphisms (flatLocalDesc ρ hcover f k hk)
    (flatLocalDesc_compatible ρ hcover f k hk)

/-- The global descent restricts to the constructed affine local descents. -/
@[reassoc]
lemma baseChart_flatDesc (c : BaseChart ρ f) :
    c.val.2.val.ι ≫ flatDesc ρ hcover f k hk = flatLocalDesc ρ hcover f k hk c :=
  (baseCover ρ f).ι_glueMorphisms _ _ c

/-- Global flat-base-change descent factors the actual invariant pullback morphism. -/
@[reassoc]
lemma flatDesc_fac : pullback.snd (map ρ hcover) f ≫ flatDesc ρ hcover f k hk = k := by
  apply (pullbackSourceCover ρ hcover f).hom_ext
  intro c
  change sourceChartMap ρ hcover f c ≫ pullback.snd _ _ ≫ _ =
    sourceChartMap ρ hcover f c ≫ k
  simp only [sourceChartMap_snd_assoc, baseChart_flatDesc, flatLocalDesc_fac]

include hk in
/-- Every invariant map descends uniquely after any flat base change of the global quotient. -/
theorem existsUnique_flatDesc : ∃! d : S ⟶ Y, pullback.snd (map ρ hcover) f ≫ d = k := by
  refine ⟨flatDesc ρ hcover f k hk, flatDesc_fac ρ hcover f k hk, ?_⟩
  intro d hd
  rw [← cancel_epi (pullback.snd (map ρ hcover) f), hd, flatDesc_fac]

/-- Flat base change preserves the full categorical quotient universal property. -/
theorem invariant_iff_existsUnique_flatDesc :
    (∀ g : G, (FiniteGroupPullback.action ρ _ (map_invariant ρ hcover) f g).hom ≫ k = k) ↔
      ∃! d : S ⟶ Y, pullback.snd (map ρ hcover) f ≫ d = k := by
  constructor
  · exact existsUnique_flatDesc ρ hcover f k
  · rintro ⟨d, hd, _⟩ g
    rw [← hd, FiniteGroupPullback.action_snd_assoc]

end FLT.Mazur.StableAffineQuotient
