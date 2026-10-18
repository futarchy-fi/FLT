/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSubgroupIdeal
public import FLT.Mazur.FiniteFlatIdealVanishingUniversal

/-!
# The closed locus of containment of two actual finite subgroups

Restrict the second subgroup ideal to the first finite locally free carrier.
Its coefficient-vanishing locus represents containment after arbitrary base
change. This retains the whole subgroup schemes, including non-etale fibers
and nonreduced bases; no choice of Cartier generator enters the construction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n m : ℕ}
  (H : E.FiniteSubgroup n) (J : E.FiniteSubgroup m)

/-- The ideal obstructing containment of the first actual subgroup in the second. -/
def containmentTestIdeal : H.carrier.left.IdealSheafData := J.ideal.comap H.curveMap.left

/-- Vanishing on the whole carrier is exactly the required order of actual subgroup ideals. -/
theorem containmentTestIdeal_eq_bot_iff :
    containmentTestIdeal H J = ⊥ ↔ J.ideal ≤ H.ideal := by
  change J.ideal.comap H.curveMap.left = ⊥ ↔ J.ideal ≤ H.curveMap.left.ker
  rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_bot]

/-- The obstruction on pulled subgroups is the pullback of the original carrier ideal. -/
theorem containmentTestIdeal_baseChange {T : Scheme} (g : T ⟶ S) :
    containmentTestIdeal (H.baseChange g) (J.baseChange g) =
      (containmentTestIdeal H J).comap (pullback.fst H.carrier.hom g) := by
  unfold containmentTestIdeal
  rw [baseChange_ideal, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, baseChange_curveMap]
  exact congrArg (fun k ↦ J.ideal.comap k) (OverPullbackLocalPushout.map_isPullback g H.curveMap).w

/-- The actual closed parameter scheme on which the first subgroup is contained in the second. -/
def containmentLocus : Scheme :=
  FiniteFlatIdealVanishing.locus H.carrier.hom (containmentTestIdeal H J)

/-- Its inclusion into the original base retains the original finite subgroup families. -/
def containmentLocusInclusion : containmentLocus H J ⟶ S :=
  FiniteFlatIdealVanishing.locusInclusion H.carrier.hom (containmentTestIdeal H J)

instance containmentLocusInclusion_closed : IsClosedImmersion (containmentLocusInclusion H J) :=
  inferInstanceAs (IsClosedImmersion
    (FiniteFlatIdealVanishing.locusInclusion H.carrier.hom (containmentTestIdeal H J)))

/-- Arbitrary tests factor precisely when their full pulled subgroups satisfy containment. -/
theorem containmentLocus_factorization_iff {T : Scheme} (g : T ⟶ S) :
    (∃ k : T ⟶ containmentLocus H J, k ≫ containmentLocusInclusion H J = g) ↔
      (J.baseChange g).ideal ≤ (H.baseChange g).ideal := by
  rw [← containmentTestIdeal_eq_bot_iff, containmentTestIdeal_baseChange]
  exact FiniteFlatIdealVanishing.locus_factorization_iff
    (IsPullback.of_hasPullback H.carrier.hom g) (containmentTestIdeal H J)

/-- Construct the actual parameter factorization from the proved subgroup containment. -/
def containmentLocusLift {T : Scheme} (g : T ⟶ S)
    (h : (J.baseChange g).ideal ≤ (H.baseChange g).ideal) : T ⟶ containmentLocus H J :=
  ((containmentLocus_factorization_iff H J g).mpr h).choose

/-- The factorization retains the supplied original base map. -/
@[reassoc] theorem containmentLocusLift_inclusion {T : Scheme} (g : T ⟶ S)
    (h : (J.baseChange g).ideal ≤ (H.baseChange g).ideal) :
    containmentLocusLift H J g h ≫ containmentLocusInclusion H J = g :=
  ((containmentLocus_factorization_iff H J g).mpr h).choose_spec

/-- The closed immersion makes every such parameter factorization unique. -/
theorem containmentLocusLift_unique {T : Scheme} (g : T ⟶ S)
    (h : (J.baseChange g).ideal ≤ (H.baseChange g).ideal) (k : T ⟶ containmentLocus H J)
    (hk : k ≫ containmentLocusInclusion H J = g) : k = containmentLocusLift H J g h := by
  apply (cancel_mono (containmentLocusInclusion H J)).mp
  rw [hk, containmentLocusLift_inclusion]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
