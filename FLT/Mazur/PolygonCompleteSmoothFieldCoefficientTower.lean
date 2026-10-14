/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientUnique
public import FLT.Mazur.OverPullbackSectionComposition

/-!
# Full DR coherence for towers of original coefficient squares

The composed field comparison is the unique full DR comparison retaining the
original total-space projection. The identity comparison has the same uniqueness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs

/-- The canonical identity comparison is forced by the actual original projection. -/
theorem completeFieldBaseChange_id_unique (i : Fin n)
    (d : (E i).baseChange (𝟙 _) ≅ E i)
    (hd : d.inv.curve.left ≫ pullback.fst q (𝟙 _) ≫ p = p) :
    d = (E i).baseChangeIdIso := by
  apply Iso.symm_eq_iff.mp
  apply Iso.ext
  apply completeFieldBaseChange_hom_ext K n h L a ha p q hs i
  change d.inv.curve.left ≫ pullback.fst q (𝟙 _) ≫ p =
    (E i).baseChangeIdIso.inv.curve.left ≫ pullback.fst q (𝟙 _) ≫ p
  rw [hd]
  erw [← baseChangeIdIso_left (E i)]
  have he := congrArg (fun f ↦ f.curve.left) (E i).baseChangeIdIso.inv_hom_id
  change (E i).baseChangeIdIso.inv.curve.left ≫
    (E i).baseChangeIdIso.hom.curve.left = 𝟙 _ at he
  rw [← Category.assoc, he, Category.id_comp]

variable (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
  (N : Type) [Field N] [Algebra M N]
  {V : Scheme} (v : V ⟶ exactVeroneseProj K n h) (w : V ⟶ Spec (.of N))
  (hv : IsPullback v w (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap M N).comp ((algebraMap L M).comp a)))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "aN" => RingHom.comp (algebraMap M N) aM
local notation "haN" => Iff.mpr (map_ne_zero (algebraMap M N)) haM
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap M N))
local notation "D" => completeFieldGeneralizedCurve K n h M aM haM r s ht
local notation "A" => completeFieldGeneralizedCurve K n h N aN haN v w hv
local notation "e" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht
local notation "f" => completeFieldCoefficientCurveIso K n h M aM haM r s ht N v w hv

/-- The actual two coefficient extensions compose as full DR isomorphisms. -/
def completeFieldCoefficientTowerIso (i : Fin n) : (E i).baseChange (c ≫ b) ≅ A i :=
  (E i).baseChangeCompIso b c ≪≫ (baseChangeFunctor c).mapIso (e i) ≪≫ f i

/-- The composed full DR comparison retains the original total-space projection. -/
@[reassoc] theorem completeFieldCoefficientTowerIso_inv_total (i : Fin n) :
    (completeFieldCoefficientTowerIso K n h L a ha p q hs M r s ht N v w hv i).inv.curve.left ≫
      pullback.fst q (c ≫ b) ≫ p = v := by
  change (f i).inv.curve.left ≫ (baseChangeMap c (e i).inv).curve.left ≫
    ((E i).baseChangeCompIso b c).inv.curve.left ≫ pullback.fst q (c ≫ b) ≫ p = v
  have hc : ((E i).baseChangeCompIso b c).inv.curve.left ≫
      pullback.fst q (c ≫ b) ≫ p =
        pullback.fst (pullback.snd q b) c ≫ pullback.fst q b ≫ p :=
    OverPullbackSection.comp_inv_fst_assoc c b (E i).curve p
  rw [hc]
  erw [baseChangeMap_fst_assoc c (e i).inv]
  rw [completeFieldCoefficientCurveIso_inv_total K n h L a ha p q hs M r s ht i]
  exact completeFieldCoefficientCurveIso_inv_total K n h M aM haM r s ht N v w hv i

/-- Every full direct comparison with the original projection equals the iterated comparison. -/
theorem completeFieldCoefficientTowerIso_unique (i : Fin n)
    (d : (E i).baseChange (c ≫ b) ≅ A i)
    (hd : d.inv.curve.left ≫ pullback.fst q (c ≫ b) ≫ p = v) :
    d = completeFieldCoefficientTowerIso K n h L a ha p q hs M r s ht N v w hv i := by
  apply Iso.symm_eq_iff.mp
  apply Iso.ext
  apply completeFieldBaseChange_hom_ext K n h L a ha p q hs i
  exact hd.trans (completeFieldCoefficientTowerIso_inv_total K n h L a ha p q hs
    M r s ht N v w hv i).symm

end FLT.Mazur.PolygonInfinitesimalStages
