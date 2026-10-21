/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationEndpointImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Full finite endpoint quotients and scheme-valued arrow tests

The full finite relation is the quotient of the affine endpoint ring by its
actual kernel. Vanishing of these equations on a test scheme constructs a
unique relation arrow with both endpoints prescribed, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationEndpointQuotientTests
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (h : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [IsSeparated f]
set_option quotPrecheck false
local notation "c" => pullback.lift p q h

/-- The actual full relation coefficient ring is an endpoint quotient, not a reduced image. -/
def endpointQuotientEquiv :
    Γ(pullback f f, ⊤) ⧸ RingHom.ker (c).appTop.hom ≃+* Γ(D, ⊤) :=
  RingHom.quotientKerEquivOfSurjective
    (FiniteRelationEndpointImmersion.endpoint_appTop_surjective p q f h e)

/-- The quotient identification retains every original endpoint coefficient. -/
theorem endpointQuotientEquiv_mk (s : Γ(pullback f f, ⊤)) :
    endpointQuotientEquiv p q f h e (Ideal.Quotient.mk _ s) = (c).appTop s := rfl

include e in
/-- Full endpoint equations construct a unique scheme arrow, with both coordinates fixed. -/
theorem existsUnique_arrow_iff {T : Scheme.{0}} (x y : T ⟶ A)
    (hxy : x ≫ f = y ≫ f) :
    (∃! d : T ⟶ D, d ≫ p = x ∧ d ≫ q = y) ↔
      RingHom.ker (c).appTop.hom ≤
        RingHom.ker (pullback.lift x y hxy).appTop.hom := by
  let t := pullback.lift x y hxy
  constructor
  · rintro ⟨d, hd, _⟩
    have he : d ≫ c = t := by
      apply (IsPullback.of_hasPullback f f).hom_ext
      · simpa only [t, Category.assoc, pullback.lift_fst] using hd.1
      · simpa only [t, Category.assoc, pullback.lift_snd] using hd.2
    intro s hs
    change t.appTop s = 0
    rw [← he, Scheme.Hom.comp_appTop]
    change d.appTop ((c).appTop s) = 0
    rw [show (c).appTop s = 0 from hs, map_zero]
  · intro ht
    let _ := FiniteRelationEndpointImmersion.endpoint_closed p q f h e
    have hk : (c).ker ≤ t.ker := by
      apply Scheme.IdealSheafData.le_of_isAffine
      simpa [Scheme.ker_of_isAffine] using ht
    let d := IsClosedImmersion.lift c t hk
    have hd : d ≫ c = t := IsClosedImmersion.lift_fac _ _ _
    have hp : d ≫ p = x := by
      simpa only [t, Category.assoc, pullback.lift_fst] using
        congrArg (fun g ↦ g ≫ pullback.fst f f) hd
    have hq : d ≫ q = y := by
      simpa only [t, Category.assoc, pullback.lift_snd] using
        congrArg (fun g ↦ g ≫ pullback.snd f f) hd
    refine ⟨d, ⟨hp, hq⟩, fun d' hd' ↦ ?_⟩
    exact e.toJointlyMono₂.right_cancellation d' d
      (hd'.1.trans hp.symm) (hd'.2.trans hq.symm)

end FLT.Mazur.FiniteRelationEndpointQuotientTests
