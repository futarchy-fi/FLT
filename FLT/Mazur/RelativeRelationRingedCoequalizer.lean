/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationRingedDescent

/-!
# The invariant ringed orbit is the ringed coequalizer

The invariant sheaf construction has the full universal property of a ringed
coequalizer. Consequently it agrees with the underlying ringed space of the
locally ringed coequalizer, not just its topological carrier.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Uniqueness of the regular-function map over the descended continuous map. -/
theorem ringedDescend_c_unique (s : Cofork p.left.toShHom q.left.toShHom)
    (c : s.pt.presheaf ⟶ (TopCat.Presheaf.pushforward _
      (ringedDescendBase e s)).obj (invariantSheaf e).obj)
    (hm : toRingedSpace e ≫ ⟨ringedDescendBase e s, c⟩ = s.π) :
    c = (ringedDescend e s).hom.c := by
  change c = (pushInvariantIsLimit e (ringedDescendBase e s)).lift
    (Fork.ofι (ringedDescendSource e s) (ringedDescendSource_condition e s))
  apply Fork.IsLimit.hom_ext (pushInvariantIsLimit e (ringedDescendBase e s))
  rw [Fork.IsLimit.lift_ι]
  apply NatTrans.ext
  funext W
  have h := PresheafedSpace.congr_app (congrArg (fun k ↦ k.hom) hm) W
  change c.app W ≫ (invariantInclusion e).hom.app _ = _ at h
  dsimp [ringedDescendSource]
  rw [TopCat.Presheaf.pushforwardEq_hom_app]
  exact h

/-- A ringed morphism can be written over any equal continuous base map. -/
theorem ringedHom_exists_fixedBase {X Y : SheafedSpace CommRingCat.{u}}
    (m : X ⟶ Y) (b : X.carrier ⟶ Y.carrier) (hb : m.hom.base = b) :
    ∃ c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward _ b).obj X.presheaf,
      m = ⟨b, c⟩ := by
  subst b
  exact ⟨m.hom.c, rfl⟩

/-- Equality over a fixed base reduces to equality of the regular-function maps. -/
theorem ringedHom_ext_fixedBase {X Y : SheafedSpace CommRingCat.{u}}
    (m n : X ⟶ Y) (hb : m.hom.base = n.hom.base)
    (hc : ∀ c : Y.presheaf ⟶ (TopCat.Presheaf.pushforward _ n.hom.base).obj X.presheaf,
      m = ⟨n.hom.base, c⟩ → c = n.hom.c) : m = n := by
  obtain ⟨c, he⟩ := ringedHom_exists_fixedBase m n.hom.base hb
  rw [he]
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  exact PresheafedSpace.hext ⟨n.hom.base, c⟩ n.hom rfl (heq_of_eq (hc c he))

/-- A descended ringed map is determined by its composite with the source projection. -/
theorem ringedDescend_unique (s : Cofork p.left.toShHom q.left.toShHom)
    (m : ringedSpace e ⟶ s.pt) (hm : toRingedSpace e ≫ m = s.π) :
    m = ringedDescend e s := by
  have hb : m.hom.base = ringedDescendBase e s := by
    apply Cofork.IsColimit.hom_ext (orbitCoforkIsColimit e)
    exact (congrArg (fun k ↦ k.hom.base) hm).trans (ringedDescendBase_fac e s).symm
  apply ringedHom_ext_fixedBase m (ringedDescend e s) hb
  intro c hc
  exact ringedDescend_c_unique e s c (hc ▸ hm)

/-- The explicit invariant ringed orbit satisfies the ringed coequalizer universal property. -/
def ringedCoforkIsColimit : IsColimit (ringedCofork e) := by
  apply Cofork.IsColimit.mk'
  intro s
  exact ⟨ringedDescend e s, ringedDescend_fac e s,
    fun {m} hm ↦ ringedDescend_unique e s m hm⟩

/-- The locally ringed quotient and invariant ringed orbit are canonically isomorphic. -/
def locallyRingedOrbitRingedIso :
    (locallyRingedQuotient (p := p) (q := q)).toSheafedSpace ≅ ringedSpace e :=
  (PreservesCoequalizer.iso LocallyRingedSpace.forgetToSheafedSpace
    p.left.toLRSHom q.left.toLRSHom).symm ≪≫
    (coequalizerIsCoequalizer p.left.toShHom q.left.toShHom).coconePointUniqueUpToIso
      (ringedCoforkIsColimit e)

/-- The ringed comparison identifies the original quotient projections. -/
theorem locallyRingedProjection_ringedIso :
    (locallyRingedProjection (p := p) (q := q)).toShHom ≫
      (locallyRingedOrbitRingedIso e).hom = toRingedSpace e := by
  dsimp only [locallyRingedOrbitRingedIso, Iso.trans_hom, Iso.symm_hom,
    locallyRingedProjection, locallyRingedQuotient]
  rw [← Category.assoc]
  erw [map_π_preserves_coequalizer_inv LocallyRingedSpace.forgetToSheafedSpace
    p.left.toLRSHom q.left.toLRSHom]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coequalizerIsCoequalizer p.left.toShHom q.left.toShHom)
    (ringedCoforkIsColimit e) WalkingParallelPair.one

end FLT.Mazur.RelativeRelationOrbit
