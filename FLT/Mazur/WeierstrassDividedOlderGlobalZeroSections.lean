/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroConic
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodes
public import FLT.Mazur.WeierstrassModificationXIncidenceSectionMaps

/-!
# Ordered incidence sections in the actual retained global model

Conic incidence sections and full ambient node origins give the same two
ordered maps to the global model. The ordering agrees with the original
split intersection, and the maps remain distinct after every retention.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- The original first node chart sends its origin to the ordered section. -/
@[reassoc] theorem zeroFirstNodeOrigin_chart {S : Type u} [CommRing S]
    (a c : S) (ha : IsUnit a) :
    Spec.map (CommRingCat.ofHom
      (WeierstrassModificationX.fullNodeOrigin a c ha).toRingHom) ≫
      WeierstrassModificationX.fullFirstNodeChart a c ha =
        Spec.map (CommRingCat.ofHom
          (WeierstrassModificationX.fullFirstIncidencePoint a c ha).toRingHom) := by
  rw [WeierstrassModificationX.fullFirstNodeChart_eq_spec, ← Spec.map_comp]
  exact congrArg (fun f : WeierstrassModificationX.FiberCoordinate a c →ₐ[S] S =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
      (WeierstrassModificationX.fullFirstNodeOrigin_comp a c ha)

/-- The original second node chart sends its origin to the ordered section. -/
@[reassoc] theorem zeroSecondNodeOrigin_chart {S : Type u} [CommRing S]
    (a c : S) (ha : IsUnit a) :
    Spec.map (CommRingCat.ofHom
      (WeierstrassModificationX.fullNodeOrigin (-a) c ha.neg).toRingHom) ≫
      WeierstrassModificationX.fullSecondNodeChart a c ha =
        Spec.map (CommRingCat.ofHom
          (WeierstrassModificationX.fullSecondIncidencePoint a c ha).toRingHom) := by
  rw [WeierstrassModificationX.fullSecondNodeChart_eq_spec, ← Spec.map_comp]
  exact congrArg (fun f : WeierstrassModificationX.FiberCoordinate a c →ₐ[S] S =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
      (WeierstrassModificationX.fullSecondNodeOrigin_comp a c ha)

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first ordered intersection section of the retained global fiber. -/
def olderGlobalZeroFirstSection :=
  Spec.map (CommRingCat.ofHom (fullFirstIncidencePoint a c ha).toRingHom) ≫ g

/-- The first global section is the original conic incidence point. -/
@[reassoc] theorem olderGlobalZeroFirstSection_conic :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫
      olderGlobalZeroConic hπ data D j hj r hr hk0 hk =
        olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroConic, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp, olderGlobalZeroFirstSection, fullFirstIncidencePoint_conic]
  rfl

/-- The first section is the fst factor of the original ordered intersection. -/
theorem olderGlobalZeroFirstSection_ordered :
    olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk =
      Spec.map (CommRingCat.ofHom
        ((AlgHom.fst K K K).comp (fiberOrderedIntersectionMap a c ha)).toRingHom) ≫ g := by
  rw [olderGlobalZeroFirstSection, fullFirstIncidencePoint_ordered]

/-- The origin of the first full ambient node gives that same ordered global section. -/
@[reassoc] theorem olderGlobalZeroFirstNode_origin :
    Spec.map (CommRingCat.ofHom (fullNodeOrigin a c ha).toRingHom) ≫
      olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk =
        olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroFirstNode, ← Category.assoc, zeroFirstNodeOrigin_chart]
  rfl

/-- The second ordered intersection section of the retained global fiber. -/
def olderGlobalZeroSecondSection :=
  Spec.map (CommRingCat.ofHom (fullSecondIncidencePoint a c ha).toRingHom) ≫ g

/-- The second global section is the original conic incidence point. -/
@[reassoc] theorem olderGlobalZeroSecondSection_conic :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫
      olderGlobalZeroConic hπ data D j hj r hr hk0 hk =
        olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroConic, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp, olderGlobalZeroSecondSection, fullSecondIncidencePoint_conic]
  rfl

/-- The second section is the snd factor of the original ordered intersection. -/
theorem olderGlobalZeroSecondSection_ordered :
    olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk =
      Spec.map (CommRingCat.ofHom
        ((AlgHom.snd K K K).comp (fiberOrderedIntersectionMap a c ha)).toRingHom) ≫ g := by
  rw [olderGlobalZeroSecondSection, fullSecondIncidencePoint_ordered]

/-- The origin of the second full ambient node gives that same ordered global section. -/
@[reassoc] theorem olderGlobalZeroSecondNode_origin :
    Spec.map (CommRingCat.ofHom (fullNodeOrigin (-a) c (ha).neg).toRingHom) ≫
      olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk =
        olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroSecondNode, ← Category.assoc, zeroSecondNodeOrigin_chart]
  rfl

/-- The first parameter origin maps to the corresponding actual global node section. -/
@[reassoc] theorem olderGlobalZeroConicFirstParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk =
        olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  have H : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c =
        Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : ConicCoordinate a c →ₐ[K] K =>
      Spec.map (CommRingCat.ofHom f.toRingHom)) (conicFirstParameterOrigin_comp a c ha)
  rw [olderGlobalZeroConicFirstParameter, ← Category.assoc, ← Category.assoc,
    Category.assoc _ _ (conicFirstOpenImmersion a c), H,
    olderGlobalZeroFirstSection_conic]

/-- The second parameter origin maps to the corresponding actual global node section. -/
@[reassoc] theorem olderGlobalZeroConicSecondParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk =
        olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  have H : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c =
        Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : ConicCoordinate a c →ₐ[K] K =>
      Spec.map (CommRingCat.ofHom f.toRingHom)) (conicSecondParameterOrigin_comp a c ha)
  rw [olderGlobalZeroConicSecondParameter, ← Category.assoc, ← Category.assoc,
    Category.assoc _ _ (conicSecondOpenImmersion a c), H,
    olderGlobalZeroSecondSection_conic]

/-- Retention never identifies the two original ordered sections. -/
theorem olderGlobalZeroSections_ne :
    olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk ≠
      olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  intro h
  have h' := (cancel_mono g).mp h
  have hv := congrArg (fun f => f.hom (fiberV a c)) (Spec.map_injective h')
  change fullFirstIncidencePoint a c ha (fiberV a c) =
    fullSecondIncidencePoint a c ha (fiberV a c) at hv
  rw [fullFirstIncidencePoint_v, fullSecondIncidencePoint_v] at hv
  exact (ha).ne_zero (neg_eq_zero.mp hv.symm)

end FLT.Mazur.WeierstrassDividedDepth
