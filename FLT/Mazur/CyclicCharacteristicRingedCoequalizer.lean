/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRingedDescent

/-!
# The invariant ringed orbit is the ringed coequalizer

The invariant sheaf construction has the full universal property of a ringed
coequalizer. Consequently it agrees with the underlying ringed space of the
locally ringed coequalizer, not just its topological carrier.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- Uniqueness of the regular-function map over the descended continuous map. -/
theorem ringedDescend_c_unique (s : Cofork (src).toShHom (tgt).toShHom)
    (c : s.pt.presheaf ⟶ (TopCat.Presheaf.pushforward _
      (ringedDescendBase n s)).obj (invariantSheaf n).obj)
    (hm : toRingedSpace n ≫ ⟨ringedDescendBase n s, c⟩ = s.π) :
    c = (ringedDescend n s).hom.c := by
  change c = (pushInvariantIsLimit n (ringedDescendBase n s)).lift
    (Fork.ofι (ringedDescendSource n s) (ringedDescendSource_condition n s))
  apply Fork.IsLimit.hom_ext (pushInvariantIsLimit n (ringedDescendBase n s))
  rw [Fork.IsLimit.lift_ι]
  apply NatTrans.ext
  funext W
  have h := PresheafedSpace.congr_app (congrArg (fun k ↦ k.hom) hm) W
  change c.app W ≫ (invariantInclusion n).hom.app _ = _ at h
  dsimp [ringedDescendSource]
  rw [TopCat.Presheaf.pushforwardEq_hom_app]
  exact h

/-- A ringed morphism can be written over any equal continuous base map. -/
theorem ringedHom_exists_fixedBase {X Y : SheafedSpace CommRingCat}
    (m : X ⟶ Y) (b : X.carrier ⟶ Y.carrier) (hb : m.hom.base = b) :
    ∃ c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward _ b).obj X.presheaf,
      m = ⟨b, c⟩ := by
  subst b
  exact ⟨m.hom.c, rfl⟩

/-- Equality over a fixed base reduces to equality of the regular-function maps. -/
theorem ringedHom_ext_fixedBase {X Y : SheafedSpace CommRingCat}
    (m n : X ⟶ Y) (hb : m.hom.base = n.hom.base)
    (hc : ∀ c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward _ n.hom.base).obj X.presheaf,
      m = ⟨n.hom.base, c⟩ → c = n.hom.c) : m = n := by
  obtain ⟨c, he⟩ := ringedHom_exists_fixedBase m n.hom.base hb
  rw [he]
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  exact PresheafedSpace.hext ⟨n.hom.base, c⟩ n.hom rfl (heq_of_eq (hc c he))

/-- A descended ringed map is determined by its composite with the source projection. -/
theorem ringedDescend_unique (s : Cofork (src).toShHom (tgt).toShHom)
    (m : ringedSpace n ⟶ s.pt) (hm : toRingedSpace n ≫ m = s.π) :
    m = ringedDescend n s := by
  have hb : m.hom.base = ringedDescendBase n s := by
    apply Cofork.IsColimit.hom_ext (orbitCoforkIsColimit n)
    exact (congrArg (fun k ↦ k.hom.base) hm).trans (ringedDescendBase_fac n s).symm
  apply ringedHom_ext_fixedBase m (ringedDescend n s) hb
  intro c hc
  exact ringedDescend_c_unique n s c (hc ▸ hm)

/-- The explicit invariant ringed orbit satisfies the ringed coequalizer universal property. -/
def ringedCoforkIsColimit : IsColimit (ringedCofork n) := by
  apply Cofork.IsColimit.mk'
  intro s
  exact ⟨ringedDescend n s, ringedDescend_fac n s,
    fun {m} hm ↦ ringedDescend_unique n s m hm⟩

/-- The locally ringed quotient and invariant ringed orbit are canonically isomorphic. -/
def locallyRingedOrbitRingedIso :
    (locallyRingedQuotient n).toSheafedSpace ≅ ringedSpace n :=
  (PreservesCoequalizer.iso LocallyRingedSpace.forgetToSheafedSpace
    (src).toLRSHom (tgt).toLRSHom).symm ≪≫
    (coequalizerIsCoequalizer (src).toShHom (tgt).toShHom).coconePointUniqueUpToIso
      (ringedCoforkIsColimit n)

/-- The ringed comparison identifies the original quotient projections. -/
theorem locallyRingedProjection_ringedIso :
    (locallyRingedProjection n).toShHom ≫
      (locallyRingedOrbitRingedIso n).hom = toRingedSpace n := by
  dsimp only [locallyRingedOrbitRingedIso, Iso.trans_hom, Iso.symm_hom,
    locallyRingedProjection, locallyRingedQuotient]
  rw [← Category.assoc]
  erw [map_π_preserves_coequalizer_inv LocallyRingedSpace.forgetToSheafedSpace
    (src).toLRSHom (tgt).toLRSHom]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coequalizerIsCoequalizer (src).toShHom (tgt).toShHom)
    (ringedCoforkIsColimit n) WalkingParallelPair.one

end FLT.Mazur.CyclicCharacteristicOrbit
