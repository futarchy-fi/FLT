/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonExteriorComparison

/-!
# Comparing the complete twisted exterior with the prescribed polygon

The actual nonterminal open unions in the original and simultaneous twisted
models are identified. Transporting the constructed exterior comparison gives
the prescribed polygon map on each normalized retained label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "ι" => simultaneousTwistedArithmeticChart hπ data H m j hj u hu
local notation "e" => twistedArithmeticAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "U" => openImageUnion
  (fun (idx : ArithmeticExteriorLabel (j + 1)) ↦ c (Subtype.val idx))
local notation "F" => arithmeticPolygonComparisonChart hπ data H m j hj u hu
local notation "Y" => arithmeticFactorRatioPolygon π m W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "a" => (fun (idx : ArithmeticExteriorLabel (j + 1)) ↦ c (Subtype.val idx))
local notation "b" => (fun (idx : ArithmeticExteriorLabel (j + 1)) ↦ ι (Subtype.val idx))

/-- The full nonterminal open union inside the simultaneous twisted target. -/
def twistedArithmeticExterior :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).Opens := openImageUnion b

/-- The global transport carries exactly the original exterior onto the normalized exterior. -/
theorem twistedArithmeticExterior_range :
    Set.range ((U).ι ≫ (G).hom) =
      (twistedArithmeticExterior hπ data H m j hj u hu : Set _) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, y, rfl⟩ := (openImageUnionCover a).exists_eq x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨i, (e i.val).hom y, ?_⟩
    have h := simultaneousTwistedArithmeticIso_chart hπ data H m j hj u hu i.val
    have hc := openImageUnionMap_fac a i
    exact (congrArg (fun f ↦ f y) (by
      rw [← Category.assoc, hc, h] :
        openImageUnionMap a i ≫ (U).ι ≫ (G).hom = (e i.val).hom ≫ ι i.val)).symm
  · intro hz
    change z ∈ openImageUnion b at hz
    obtain ⟨i, y, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    refine ⟨openImageUnionMap a i ((e i.val).inv y), ?_⟩
    have h : (e i.val).inv ≫ openImageUnionMap a i ≫ (U).ι ≫ (G).hom = ι i.val := by
      rw [openImageUnionMap_fac_assoc, simultaneousTwistedArithmeticIso_chart,
        Iso.inv_hom_id_assoc]
    exact congrArg (fun f ↦ f y) h

/-- The actual open-union identification is induced by the constructed global isomorphism. -/
def twistedArithmeticExteriorIso :
    (U).toScheme ≅ (twistedArithmeticExterior hπ data H m j hj u hu).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((U).ι ≫ (G).hom)
    (twistedArithmeticExterior hπ data H m j hj u hu).ι (by
      rw [Scheme.Opens.range_ι, twistedArithmeticExterior_range])

/-- The union identification recovers the original simultaneous global comparison. -/
@[reassoc] theorem twistedArithmeticExteriorIso_global :
    (twistedArithmeticExteriorIso hπ data H m j hj u hu).hom ≫
      (twistedArithmeticExterior hπ data H m j hj u hu).ι = (U).ι ≫ (G).hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Every normalized exterior chart retains its full original chart comparison. -/
@[reassoc] theorem twistedArithmeticExteriorIso_chart
    (i : ArithmeticExteriorLabel (j + 1)) :
    openImageUnionMap a i ≫ (twistedArithmeticExteriorIso hπ data H m j hj u hu).hom =
      (e i.val).hom ≫ openImageUnionMap b i := by
  apply (cancel_mono (twistedArithmeticExterior hπ data H m j hj u hu).ι).mp
  rw [Category.assoc, twistedArithmeticExteriorIso_global,
    openImageUnionMap_fac_assoc, Category.assoc]
  change c i.val ≫ (G).hom =
    (e i.val).hom ≫ openImageUnionMap b i ≫ (openImageUnion b).ι
  rw [openImageUnionMap_fac, simultaneousTwistedArithmeticIso_chart]

/-- The simultaneous twisted exterior has a constructed map to the prescribed polygon. -/
def twistedArithmeticExteriorPolygonMap :
    (twistedArithmeticExterior hπ data H m j hj u hu).toScheme ⟶ Y :=
  (twistedArithmeticExteriorIso hπ data H m j hj u hu).inv ≫
    arithmeticPolygonExteriorMap hπ data H m j hj u hu

/-- Each entire normalized chart has the transported original corrected polygon map. -/
@[reassoc] theorem twistedArithmeticExteriorPolygonMap_chart
    (i : ArithmeticExteriorLabel (j + 1)) :
    openImageUnionMap b i ≫ twistedArithmeticExteriorPolygonMap hπ data H m j hj u hu =
      (e i.val).inv ≫ F i.val := by
  apply (cancel_epi (e i.val).hom).mp
  rw [← Category.assoc, ← twistedArithmeticExteriorIso_chart,
    twistedArithmeticExteriorPolygonMap, Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticPolygonExteriorMap_chart, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
