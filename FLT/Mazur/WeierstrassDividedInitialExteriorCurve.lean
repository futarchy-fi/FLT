/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialIncidenceInfinity
public import FLT.Mazur.SchemeOpenPushoutIntersection

/-!
# Gluing the complete exterior incidence line to the original infinity chart

The full incidence line and unchanged infinity chart glue along their proved
exact slope intersection. The resulting scheme maps to the actual retained
model, with both original initial nodes. Identifying this curve with the
projective line is a further comparison, not an input to this construction.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "ha" => residue_tangent_isUnit D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data j hj

local notation "g" => initialGlobalResidueFiberChart hπ data D j hj hstart hk
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => initialGlobalSlopeToInfinity hπ data D j hj hstart hk
local notation "i" => finiteInfinityTensorChart hπ data K j hj
local notation "L" => initialGlobalIncidenceLine hπ data D j hj hstart hk

/-- The actual exterior curve obtained from the full incidence and infinity charts. -/
def initialExteriorCurve : Scheme.{u} := pushout s t

/-- The full incidence line is the affine chart of the constructed exterior curve. -/
def initialExteriorAffineChart : Spec (.of (Polynomial K)) ⟶
    initialExteriorCurve hπ data D j hj hstart hk := pushout.inl s t

/-- The unchanged original infinity chart is the other chart of the exterior curve. -/
def initialExteriorInfinityChart :
    Spec (.of (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) ⟶
      initialExteriorCurve hπ data D j hj hstart hk := pushout.inr s t

instance initialExteriorAffineChart_isOpenImmersion :
    IsOpenImmersion (initialExteriorAffineChart hπ data D j hj hstart hk) :=
  inferInstanceAs (IsOpenImmersion (pushout.inl s t))

instance initialExteriorInfinityChart_isOpenImmersion :
    IsOpenImmersion (initialExteriorInfinityChart hπ data D j hj hstart hk) :=
  inferInstanceAs (IsOpenImmersion (pushout.inr s t))

/-- The exterior gluing maps to the original global fiber by its exact overlap certificate. -/
def initialExteriorToGlobal : initialExteriorCurve hπ data D j hj hstart hk ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  pushout.desc L i (initialGlobalSlopeToInfinity_comp hπ data D j hj hstart hk).symm

/-- The exterior comparison retains the whole original incidence line. -/
@[reassoc] theorem initialExteriorToGlobal_affine :
    initialExteriorAffineChart hπ data D j hj hstart hk ≫
      initialExteriorToGlobal hπ data D j hj hstart hk = L :=
  pushout.inl_desc _ _ _

/-- The exterior comparison retains the whole original infinity tensor chart. -/
@[reassoc] theorem initialExteriorToGlobal_infinity :
    initialExteriorInfinityChart hπ data D j hj hstart hk ≫
      initialExteriorToGlobal hπ data D j hj hstart hk = i :=
  pushout.inr_desc _ _ _

/-- The two original charts intersect in exactly the full punctured slope scheme. -/
theorem initialExteriorCharts_isPullback :
    IsPullback s t (initialExteriorAffineChart hπ data D j hj hstart hk)
      (initialExteriorInfinityChart hπ data D j hj hstart hk) :=
  SchemeOpenPushout.isPullback s t

/-- The constructed exterior has exactly the union of the incidence and infinity images. -/
theorem initialExteriorToGlobal_range :
    Set.range (initialExteriorToGlobal hπ data D j hj hstart hk) =
      Set.range L ∪ Set.range i := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    rcases SchemeOpenPushout.charts_cover s t v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact Or.inl ⟨w, congrArg (fun morphism => morphism w)
        (initialExteriorToGlobal_affine hπ data D j hj hstart hk).symm⟩
    · exact Or.inr ⟨w, congrArg (fun morphism => morphism w)
        (initialExteriorToGlobal_infinity hπ data D j hj hstart hk).symm⟩
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact ⟨initialExteriorAffineChart hπ data D j hj hstart hk w,
        congrArg (fun morphism => morphism w)
          (initialExteriorToGlobal_affine hπ data D j hj hstart hk)⟩
    · exact ⟨initialExteriorInfinityChart hπ data D j hj hstart hk w,
        congrArg (fun morphism => morphism w)
          (initialExteriorToGlobal_infinity hπ data D j hj hstart hk)⟩

/-- The first affine marking on the constructed exterior is the actual first initial node. -/
@[reassoc] theorem initialExteriorToGlobal_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      initialExteriorAffineChart hπ data D j hj hstart hk ≫
        initialExteriorToGlobal hπ data D j hj hstart hk =
          initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialExteriorToGlobal_affine, initialGlobalIncidenceLine_first]

/-- The opposite affine marking is the actual second initial node with slope minus a₁. -/
@[reassoc] theorem initialExteriorToGlobal_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫
      initialExteriorAffineChart hπ data D j hj hstart hk ≫
        initialExteriorToGlobal hπ data D j hj hstart hk =
          initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialExteriorToGlobal_affine, initialGlobalIncidenceLine_second]

/-- The actual exterior structure map to the original residue field. -/
def initialExteriorStructure : initialExteriorCurve hπ data D j hj hstart hk ⟶ Spec (.of K) :=
  initialExteriorToGlobal hπ data D j hj hstart hk ≫ pullback.fst q f

/-- The exterior structure restricts to the original coefficient map on the whole affine line. -/
@[reassoc] theorem initialExteriorStructure_affine :
    initialExteriorAffineChart hπ data D j hj hstart hk ≫
      initialExteriorStructure hπ data D j hj hstart hk =
        Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))) := by
  rw [initialExteriorStructure, initialExteriorToGlobal_affine_assoc,
    initialGlobalIncidenceLine_structure]

/-- The exterior structure also retains the original infinity tensor coefficients. -/
@[reassoc] theorem initialExteriorStructure_infinity :
    initialExteriorInfinityChart hπ data D j hj hstart hk ≫
      initialExteriorStructure hπ data D j hj hstart hk =
        Spec.map (CommRingCat.ofHom
          (algebraMap K (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) := by
  rw [initialExteriorStructure, initialExteriorToGlobal_infinity_assoc,
    finiteInfinityTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
