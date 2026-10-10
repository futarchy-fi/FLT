/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientPullbackCharts
public import FLT.Mazur.SchemeQuotientAffineFlatDescent

/-!
# Local descent and global cancellation after flat quotient base change

The constructed equivariant affine charts give actual local descents to any
scheme target. They also prove that the global pullback projection is an
epimorphism, without assuming that the new base is affine or separated.
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

/-- The global flat-base-change projection is an epimorphism in the category of schemes. -/
instance flatPullback_snd_epi : Epi (pullback.snd (map ρ hcover) f) where
  left_cancellation a b h := by
    apply (baseCover ρ f).hom_ext
    intro c
    apply (cancel_epi (pullback.snd (quotientMap (action ρ c.val.1))
      (baseChartMap ρ f c))).mp
    change pullback.snd _ _ ≫ c.val.2.val.ι ≫ a = pullback.snd _ _ ≫ c.val.2.val.ι ≫ b
    rw [← sourceChartMap_snd_assoc ρ hcover f c,
      ← sourceChartMap_snd_assoc ρ hcover f c, h]

variable {Y : Scheme.{u}} (k : pullback (map ρ hcover) f ⟶ Y)
variable (hk : ∀ g : G, (FiniteGroupPullback.action ρ _ (map_invariant ρ hcover) f g).hom ≫
  k = k)

include hk in
omit [Flat f] in
/-- Restricting the invariant map to an actual affine source chart retains invariance. -/
lemma flatChart_invariant (c : BaseChart ρ f) (g : G) :
    (sourceChartAction ρ f c g).hom ≫ sourceChartMap ρ hcover f c ≫ k =
      sourceChartMap ρ hcover f c ≫ k := by
  rw [sourceChartMap_equivariant_assoc, hk]

/-- The actual local descended morphism on each constructed affine base chart. -/
def flatLocalDesc (c : BaseChart ρ f) : c.val.2.val.toScheme ⟶ Y :=
  SchemeQuotientAffineBase.desc (action ρ c.val.1) (baseChartMap ρ f c)
    (sourceChartMap ρ hcover f c ≫ k) (flatChart_invariant ρ hcover f k hk c)

/-- The local descended map factors the invariant map on the actual affine pullback source. -/
@[reassoc]
lemma flatLocalDesc_fac (c : BaseChart ρ f) :
    pullback.snd (quotientMap (action ρ c.val.1)) (baseChartMap ρ f c) ≫
      flatLocalDesc ρ hcover f k hk c = sourceChartMap ρ hcover f c ≫ k :=
  SchemeQuotientAffineBase.desc_fac _ _ _ _

/-- Any global factorization restricts to the constructed local factorization on each chart. -/
lemma flatLocalDesc_unique (c : BaseChart ρ f) (d : S ⟶ Y)
    (hd : pullback.snd (map ρ hcover) f ≫ d = k) :
    c.val.2.val.ι ≫ d = flatLocalDesc ρ hcover f k hk c := by
  rw [← cancel_epi (pullback.snd (quotientMap (action ρ c.val.1)) (baseChartMap ρ f c)),
    flatLocalDesc_fac, ← sourceChartMap_snd_assoc, hd]

end FLT.Mazur.StableAffineQuotient
