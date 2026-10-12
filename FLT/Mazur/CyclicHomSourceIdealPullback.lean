/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSourcePullback
public import FLT.Mazur.CyclicMarkingDivisorTransport

/-!
# The full cyclic source ideal under parameter pullback

The actual cartesian curve map pulls back the full product ideal, with one
factor for every label. No reduction or distinctness of labels is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)

/-- The original source-curve map induced by an arbitrary parameter change. -/
def cyclicHomSourcePullbackMap :
    (cyclicHomSourceCurve n (k ≫ f)).curve.left ⟶ (cyclicHomSourceCurve n f).curve.left :=
  (cyclicHomSourcePullbackIso n f k).hom.curve.left ≫
    pullback.fst (cyclicHomSourceCurve n f).curve.hom k

/-- The source-curve comparison is over the given parameter map. -/
@[reassoc] theorem cyclicHomSourcePullbackMap_base :
    cyclicHomSourcePullbackMap n f k ≫ (cyclicHomSourceCurve n f).curve.hom =
      (cyclicHomSourceCurve n (k ≫ f)).curve.hom ≫ k := by
  rw [cyclicHomSourcePullbackMap, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ k) (cyclicHomSourcePullbackIso n f k).hom.curve.w

/-- The reconstructed curve is the actual cartesian source family. -/
theorem cyclicHomSourcePullbackMap_isPullback :
    IsPullback (cyclicHomSourcePullbackMap n f k)
      (cyclicHomSourceCurve n (k ≫ f)).curve.hom (cyclicHomSourceCurve n f).curve.hom k :=
  IsPullback.of_iso_pullback ⟨cyclicHomSourcePullbackMap_base n f k⟩
    ((Over.forget U).mapIso (curveIso (cyclicHomSourcePullbackIso n f k)))
    rfl (cyclicHomSourcePullbackIso n f k).hom.curve.w

/-- Every multiplicity in the cyclic divisor is retained by the cartesian source map. -/
theorem cyclicHomSourceIdeal_pullback :
    cyclicHomSourceIdeal n (k ≫ f) =
      (cyclicHomSourceIdeal n f).comap (cyclicHomSourcePullbackMap n f k) := by
  have hm (i : Multiplicative (ZMod n)) :
      pullCyclicMarking k (cyclicHomSourceMarking n f) i ≫
        (cyclicHomSourcePullbackIso n f k).inv.group = cyclicHomSourceMarking n (k ≫ f) i := by
    rw [← cyclicHomSourcePullbackIso_marking n f k i]
    change (_ ≫ (groupIso (cyclicHomSourcePullbackIso n f k)).hom) ≫
      (groupIso (cyclicHomSourcePullbackIso n f k)).inv = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi := cyclicMarkingIdeal_transport
    (pullCyclicMarking k (cyclicHomSourceMarking n f))
    (cyclicHomSourceMarking n (k ≫ f)) (cyclicHomSourcePullbackIso n f k).symm hm
  rw [cyclicMarkingIdeal_baseChange] at hi
  exact hi.trans (Scheme.IdealSheafData.comap_comp _ _ _).symm

end FLT.Mazur.UniversalWeierstrass
