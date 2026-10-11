/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorBranches
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorBranches
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedInitialExteriorCurve
import all FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart

/-!
# Initial and infinity descents agree on the entire original punctured slope

The original initial/infinity pullback is the twice-punctured incidence line.
Its full incidence restriction agrees with the exterior gluing relation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "hk0" => (Nat.le_trans (Nat.mul_le_mul_left 2
  (Nat.le_trans (Nat.le_add_right start s) (Nat.le_succ (start + s)))) hk)
local notation "E" => residueFiberIso D start hstart hk0
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "V" => finiteInitialTensorAtlasIso hπ data K (s + 1) hs
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "g" => initialGlobalResidueFiberChart hπ data D (s + 1) hs hstart hk0
local notation "i" => finiteInfinityTensorChart hπ data K (s + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ j, ProjectiveLine.zero (ResidueField R) ≫ F j =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) j))
local notation "d" => positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w

/-- The two full exterior charts agree on their actual slope intersection. -/
@[reassoc] theorem positiveEqualityExteriorSlope_condition :
    initialGlobalSlopeToInfinity hπ data D (s + 1) hs hstart hk0 ≫
      initialExteriorInfinityChart hπ data D (s + 1) hs hstart hk0 =
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (SlopeOpen a))) ≫
      initialExteriorAffineChart hπ data D (s + 1) hs hstart hk0 :=
  (initialExteriorCharts_isPullback hπ data D (s + 1) hs hstart hk0).w.symm

/-- The full punctured slope has the prescribed exterior restriction. -/
@[reassoc] theorem positiveEqualityCycleInfinityDesc_slope :
    initialGlobalSlopeToInfinity hπ data D (s + 1) hs hstart hk0 ≫
      positiveEqualityCycleInfinityDesc hπ data D s hs hstart hk F =
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) (SlopeOpen a))) ≫
      ProjectiveLine.left K ≫
        (ProjectiveLine.slopeNormalizationIso
          (Units.mk0 a (IsUnit.ne_zero (residue_tangent_isUnit D)))).hom ≫ F 0 := by
  simp only [positiveEqualityCycleInfinityDesc]
  rw [positiveEqualityExteriorSlope_condition_assoc hπ data D s hs hstart hk,
    initialExteriorOrientedIso_affine_assoc]

/-- The distinct original initial chart is compatible with infinity on its exact pullback. -/
theorem positiveEqualityAtlasCompatible_initial_infinity :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w
      ⟨s + 3, by omega⟩ 0 := by
  apply positiveEqualityAtlasCompatible_symm hπ data D s hs hstart hk hp F w
  apply pullback_compatible_of_source_isos (Iso.refl _) ((E).trans V) i g
    (m 0) (m ⟨s + 3, by omega⟩) (d 0) (d ⟨s + 3, by omega⟩) rfl
  · apply heq_of_eq
    exact Category.id_comp _
  · apply heq_of_eq
    have H := congrArg (fun f => (E).hom ≫ f)
      (globalInitialTensorChart_eq_index hπ data K (s + 1) hs)
    simpa only [Iso.trans_hom, Category.assoc, initialGlobalResidueFiberChart,
      Fin.succ_mk, Nat.add_assoc] using H
  · let H := initialGlobalSlopeInfinity_isPullback hπ data D (s + 1) hs hstart hk0
    apply (cancel_epi H.isoPullback.hom).mp
    simp only [Iso.refl_hom, Iso.trans_hom, Category.id_comp,
      Category.assoc, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc]
    rw [positiveEqualityCycleAtlasFamily_initial, positiveEqualityCycleAtlasFamily_infinity]
    change _ = _ ≫ fiberIncidenceImmersion a c ≫ (E).hom ≫
      positiveEqualityInitialTensorDesc hπ data D s hs hstart hk F w
    rw [positiveEqualityInitialTensorDesc_incidence]
    exact positiveEqualityCycleInfinityDesc_slope hπ data D s hs hstart hk F

end FLT.Mazur.WeierstrassDividedDepth
