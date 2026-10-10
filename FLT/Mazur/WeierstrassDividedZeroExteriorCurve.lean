/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroIncidenceInfinity
public import FLT.Mazur.SchemeOpenPushoutIntersection

/-!
# The actual positive-stage start-zero exterior curve

The first retained incidence line and the unchanged infinity chart glue along
their exact original slope intersection. Both markings are the actual retained
start-zero node sections. The construction works at every later finite stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => olderGlobalZeroSlopeToInfinity hπ data D j hj r hr hk0 hk
local notation "i" => finiteInfinityTensorChart hπ data K (j + 1 + r) hr
local notation "L" => olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk

/-- The actual exterior curve obtained from the full incidence and infinity charts. -/
def zeroRetainedExteriorCurve : Scheme.{u} := pushout s t

/-- The full incidence line is the affine chart of the constructed exterior curve. -/
def zeroRetainedExteriorAffineChart : Spec (.of (Polynomial K)) ⟶
    zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk := pushout.inl s t

/-- The unchanged original infinity chart is the other chart of the exterior curve. -/
def zeroRetainedExteriorInfinityChart :
    Spec (.of (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) ⟶
      zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk := pushout.inr s t

instance zeroRetainedExteriorAffineChart_isOpenImmersion :
    IsOpenImmersion (zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (pushout.inl s t))

instance zeroRetainedExteriorInfinityChart_isOpenImmersion :
    IsOpenImmersion (zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (pushout.inr s t))

/-- The exterior gluing maps to the original global fiber by its exact overlap certificate. -/
def zeroRetainedExteriorToGlobal : zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk ⟶
    finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  pushout.desc L i (zeroRetainedIncidenceInfinity_comp hπ data D j hj r hr hk0 hk).symm

/-- The exterior comparison retains the whole original incidence line. -/
@[reassoc] theorem zeroRetainedExteriorToGlobal_affine :
    zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk ≫
      zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk = L :=
  pushout.inl_desc _ _ _

/-- The exterior comparison retains the whole original infinity tensor chart. -/
@[reassoc] theorem zeroRetainedExteriorToGlobal_infinity :
    zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk ≫
      zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk = i :=
  pushout.inr_desc _ _ _

/-- The two original charts intersect in exactly the full punctured slope scheme. -/
theorem zeroRetainedExteriorCharts_isPullback :
    IsPullback s t (zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk)
      (zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk) :=
  SchemeOpenPushout.isPullback s t

/-- The constructed exterior has exactly the union of the incidence and infinity images. -/
theorem zeroRetainedExteriorToGlobal_range :
    Set.range (zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk) =
      Set.range L ∪ Set.range i := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    rcases SchemeOpenPushout.charts_cover s t v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact Or.inl ⟨w, congrArg (fun morphism => morphism w)
        (zeroRetainedExteriorToGlobal_affine hπ data D j hj r hr hk0 hk).symm⟩
    · exact Or.inr ⟨w, congrArg (fun morphism => morphism w)
        (zeroRetainedExteriorToGlobal_infinity hπ data D j hj r hr hk0 hk).symm⟩
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact ⟨zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk w,
        congrArg (fun morphism => morphism w)
          (zeroRetainedExteriorToGlobal_affine hπ data D j hj r hr hk0 hk)⟩
    · exact ⟨zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk w,
        congrArg (fun morphism => morphism w)
          (zeroRetainedExteriorToGlobal_infinity hπ data D j hj r hr hk0 hk)⟩

/-- The first marking is the actual first retained start-zero node. -/
@[reassoc] theorem zeroRetainedExteriorToGlobal_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk ≫
        zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk =
          olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedExteriorToGlobal_affine, zeroRetainedIncidence_first]

/-- The second marking is the actual second retained start-zero node with slope minus a₁. -/
@[reassoc] theorem zeroRetainedExteriorToGlobal_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫
      zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk ≫
        zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk =
          olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedExteriorToGlobal_affine, zeroRetainedIncidence_second]

/-- The actual exterior structure map to the original residue field. -/
def zeroRetainedExteriorStructure :
    zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk ⟶ Spec (.of K) :=
  zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk ≫ pullback.fst q f

/-- The exterior structure restricts to the original coefficient map on the whole affine line. -/
@[reassoc] theorem zeroRetainedExteriorStructure_affine :
    zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk ≫
      zeroRetainedExteriorStructure hπ data D j hj r hr hk0 hk =
        Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
  rw [zeroRetainedExteriorStructure, zeroRetainedExteriorToGlobal_affine_assoc,
    zeroRetainedIncidence_structure]

/-- The exterior structure also retains the original infinity tensor coefficients. -/
@[reassoc] theorem zeroRetainedExteriorStructure_infinity :
    zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk ≫
      zeroRetainedExteriorStructure hπ data D j hj r hr hk0 hk =
        Spec.map (CommRingCat.ofHom
          (algebraMap K (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) := by
  rw [zeroRetainedExteriorStructure, zeroRetainedExteriorToGlobal_infinity_assoc,
    finiteInfinityTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
