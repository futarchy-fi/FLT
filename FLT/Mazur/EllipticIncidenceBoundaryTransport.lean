/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryRange
public import FLT.Mazur.EllipticFiniteTensorAtlasTransport
public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection

/-!
# The original incidence boundary at adjacent and terminal stages

The raw tensor incidence open retains its whole image before any node normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n)
  (hjNext : j + 2 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "F" => ResidueField A
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "eNext" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "v" => WeierstrassSuccessiveX.coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "I" => PrincipalOpenTensor.transitionIso F x t
  (WeierstrassSuccessiveX.depthOverlapEquiv W π (start + j)
    (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "J" => PrincipalOpenTensor.transitionIso F x v (previousBoundaryEquiv hπ e eNext)
local notation "b" => PrincipalOpenTensor.inclusion F t ≫
  adjacentRetainedOldGlobalTensorChart hπ data F j hj r hr
local notation "next" => finiteRetainedBoundaryTensorChart A hπ data (j + 1) hjNext r hr F

/-- The original incidence open is exactly the next retained arithmetic boundary. -/
theorem adjacentIncidenceBoundary_range_eq_retained : Set.range b = Set.range next := by
  rw [finiteRetainedBoundaryTensorChart_range]
  have h := congrArg (fun f : _ ⟶ _ => Set.range f)
    (adjacentRetainedGlobalTensor_boundary hπ data F j hj hjNext r hr)
  exact (SchemeOpenChartRange.range_iso_comp (I).symm _).symm.trans
    (h.trans (SchemeOpenChartRange.range_iso_comp (J).symm _))

/-- Reassociation preserves the raw original incidence boundary. -/
theorem olderIncidenceBoundary_reassociate :
    (PrincipalOpenTensor.inclusion F t ≫
      olderGlobalTensorChart hπ data F j hj (r + 1) (by omega)) ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + (r + 1)) (j + 2 + r)
        (by omega) hr (by omega)).hom = b := by
  rw [Category.assoc, finiteTensorIndexIso_eqToHom]
  have h : olderGlobalTensorChart hπ data F j hj (r + 1) (by omega) ≫
      eqToHom (finiteGlobalTensorModel_index_congr hπ data F (by omega) hr
        (show j + 1 + (r + 1) = j + 2 + r by omega)) =
      adjacentRetainedOldGlobalTensorChart hπ data F j hj r hr :=
    eq_of_heq ((comp_eqToHom_heq _ _).trans
      (adjacentRetainedOldGlobalTensorChart_heq hπ data F j hj r hr))
  exact congrArg (fun f => PrincipalOpenTensor.inclusion F t ≫ f) h

/-- The whole incidence image equals the next arithmetic boundary at any equal final stage. -/
theorem olderIncidenceBoundary_final_range_eq_next
    (m : ℕ) (hm : m ≤ n) (he : j + 2 + r = m) :
    Set.range ((PrincipalOpenTensor.inclusion F t ≫
      olderGlobalTensorChart hπ data F j hj (r + 1) (by omega)) ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + (r + 1)) m
        (by omega) hm (by omega)).hom) =
    Set.range (next ≫
      (finiteTensorIndexIso A hπ data F (j + 2 + r) m hr hm he).hom) := by
  rw [← finiteTensorIndexIso_comp A hπ data F (by omega) hr hm (by omega) he,
    ← Category.assoc, olderIncidenceBoundary_reassociate]
  simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] using
    congrArg (fun s => (finiteTensorIndexIso A hπ data F (j + 2 + r) m hr hm he).hom '' s)
      (adjacentIncidenceBoundary_range_eq_retained A hπ data j hj hjNext r hr)

/-- Changing an equal retention count keeps the full original incidence map. -/
theorem olderIncidenceBoundary_final_retention_congr
    (m s : ℕ) (hm : m ≤ n) (hr' : j + 1 + (r + 1) ≤ n)
    (hs : j + 1 + s ≤ n) (he : j + 1 + (r + 1) = m) (he' : j + 1 + s = m)
    (hrs : r + 1 = s) :
    (PrincipalOpenTensor.inclusion F t ≫ olderGlobalTensorChart hπ data F j hj (r + 1) hr') ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + (r + 1)) m hr' hm he).hom =
    (PrincipalOpenTensor.inclusion F t ≫ olderGlobalTensorChart hπ data F j hj s hs) ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + s) m hs hm he').hom := by
  subst s
  rfl

/-- The final original incidence boundary lies entirely in the divided terminal member. -/
theorem lastIncidenceBoundary_range_subset_terminal :
    Set.range (PrincipalOpenTensor.inclusion F t ≫
      olderGlobalTensorChart hπ data F j hj 0 hj) ⊆
    Set.range (globalDividedTensorChart hπ data F (j + 1) hj) := by
  rw [olderGlobalTensorChart_zero_retention, ← globalTensor_depthOverlap hπ data F j hj]
  rintro z ⟨w, rfl⟩
  exact ⟨_, rfl⟩

/-- Equal-stage transport retains the final incidence inclusion in the terminal chart. -/
theorem lastIncidenceBoundary_final_range_subset
    (s m : ℕ) (hs : j + 1 + s ≤ n) (hm : m ≤ n)
    (he : j + 1 + s = m) (hlast : j + 1 = m) :
    Set.range ((PrincipalOpenTensor.inclusion F t ≫
      olderGlobalTensorChart hπ data F j hj s hs) ≫
      (finiteTensorIndexIso A hπ data F (j + 1 + s) m hs hm he).hom) ⊆
    Set.range (globalDividedTensorChart hπ data F m hm) := by
  have hs0 : s = 0 := by omega
  subst s
  subst m
  simpa only [finiteTensorIndexIso, Iso.refl_hom, Category.comp_id] using
    lastIncidenceBoundary_range_subset_terminal A hπ data j hj

end FLT.Mazur.WeierstrassDividedDepth
