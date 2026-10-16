/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonExteriorComparison
public import FLT.Mazur.WeierstrassDividedPolygonComparisonRestriction

/-!
# Arithmetic restriction on the entire polygon exterior

The original global quotient map restricts to the actual union of all
nonterminal labels. The glued comparison follows this map at every order;
no closing-edge hypothesis is needed for the exterior system.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
local notation "c" => fun m ↦ arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "U" => fun m ↦ openImageUnion
  (fun (idx : ArithmeticExteriorLabel (j + 1)) ↦ c m (Subtype.val idx))
local notation "r" => fun m ↦ arithmeticLabeledAtlasRestriction hπ data H m (j + 1) hj
local notation "q" => finiteGlobalArithmeticRestriction hπ data (j + 1) hj
local notation "ι" => fun m ↦ openImageUnionMap
  (fun (idx : ArithmeticExteriorLabel (j + 1)) ↦ c m (Subtype.val idx))

/-- The original global quotient arrow maps the whole exterior into the next exterior. -/
def arithmeticPolygonExteriorRestriction (m : ℕ) :
    (U m).toScheme ⟶ (U (m + 1)).toScheme :=
  IsOpenImmersion.lift (U (m + 1)).ι ((U m).ι ≫ q m) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨idx, y, rfl⟩ := (openImageUnionCover
      (fun idx : ArithmeticExteriorLabel (j + 1) ↦ c m idx.val)).exists_eq x
    rw [Scheme.Opens.range_ι]
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨idx, r m idx.val y, ?_⟩
    have h : ι m idx ≫ (U m).ι ≫ q m = r m idx.val ≫ c (m + 1) idx.val := by
      rw [openImageUnionMap_fac_assoc, arithmeticLabeledAtlasMap_restriction]
    exact (congrArg (fun f ↦ f y) h).symm)

/-- Restriction on the exterior retains the unchanged global arithmetic quotient map. -/
@[reassoc] theorem arithmeticPolygonExteriorRestriction_global (m : ℕ) :
    arithmeticPolygonExteriorRestriction hπ data H j hj m ≫ (U (m + 1)).ι =
      (U m).ι ≫ q m := IsOpenImmersion.lift_fac _ _ _

/-- Every original chart coefficient map is retained by the restricted global arrow. -/
@[reassoc] theorem arithmeticPolygonExteriorRestriction_chart
    (m : ℕ) (idx : ArithmeticExteriorLabel (j + 1)) :
    ι m idx ≫ arithmeticPolygonExteriorRestriction hπ data H j hj m =
      r m idx.val ≫ ι (m + 1) idx := by
  apply (cancel_mono (U (m + 1)).ι).mp
  rw [Category.assoc, arithmeticPolygonExteriorRestriction_global,
    openImageUnionMap_fac_assoc, Category.assoc, openImageUnionMap_fac,
    arithmeticLabeledAtlasMap_restriction]

variable (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => fun m ↦ arithmeticPolygonExteriorMap hπ data H m j hj u hu
local notation "t" => fun m ↦ arithmeticFactorRatioPolygonRestriction π m W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)

/-- The complete exterior comparison commutes with the actual consecutive quotient arrow. -/
@[reassoc] theorem arithmeticPolygonExteriorMap_restriction (m : ℕ) :
    arithmeticPolygonExteriorRestriction hπ data H j hj m ≫ F (m + 1) = F m ≫ t m := by
  apply openImageUnion_hom_ext
    (fun idx : ArithmeticExteriorLabel (j + 1) ↦ c m idx.val)
  intro idx
  rw [arithmeticPolygonExteriorRestriction_chart_assoc,
    arithmeticPolygonExteriorMap_chart, arithmeticPolygonExteriorMap_chart_assoc,
    arithmeticPolygonComparisonChart_restriction]

/-- The actual exterior open unions form a system under the original quotient arrows. -/
def arithmeticPolygonExteriorSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (arithmeticPolygonExteriorRestriction hπ data H j hj)

/-- The original exterior system embeds naturally into the complete global arithmetic system. -/
def arithmeticPolygonExteriorSystemInclusion :
    arithmeticPolygonExteriorSystem hπ data H j hj ⟶
      finiteGlobalArithmeticSystem hπ data (j + 1) hj :=
  NatTrans.ofSequence (fun m ↦ (U m).ι) (by
    intro m
    simpa only [arithmeticPolygonExteriorSystem, finiteGlobalArithmeticSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticPolygonExteriorRestriction_global hπ data H j hj m)

/-- The glued comparison is a constructed morphism of the entire exterior quotient systems. -/
def arithmeticPolygonExteriorSystemMap :
    arithmeticPolygonExteriorSystem hπ data H j hj ⟶
      arithmeticComparisonPolygonSystem data H j :=
  NatTrans.ofSequence F (by
    intro m
    simpa only [arithmeticPolygonExteriorSystem, arithmeticComparisonPolygonSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
        arithmeticPolygonExteriorMap_restriction hπ data H j hj u hu m)

/-- All nonadjacent quotient orders retain the full glued exterior comparison. -/
@[reassoc] theorem arithmeticPolygonExteriorSystemMap_naturality {a b : ℕ} (hab : a ≤ b) :
    (arithmeticPolygonExteriorSystem hπ data H j hj).map (homOfLE hab) ≫ F b =
      F a ≫ (arithmeticComparisonPolygonSystem data H j).map (homOfLE hab) :=
  (arithmeticPolygonExteriorSystemMap hπ data H j hj u hu).naturality (homOfLE hab)

end FLT.Mazur.WeierstrassDividedDepth
