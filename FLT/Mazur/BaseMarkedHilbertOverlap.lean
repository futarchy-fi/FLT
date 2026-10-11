/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertIntersection

/-!
# Open scheme transitions over an arbitrary translation base

The intersection requires equality of the original Picard classes and of
the maps to the translation base. Both projections are open immersions.
This is distinct from the full relation after forgetting the base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))

/-- A degree and an original base Picard section specify a translated Hilbert chart. -/
abbrev BaseMarkedHilbertIndex (V : Over (Spec (.of R))) :=
  ℕ × (relativeFppfSheaf f).obj.obj (op V)

variable [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) (i j : BaseMarkedHilbertIndex f V)

/-- The original Picard section on the actual translated chart. -/
def baseMarkedChartSection :
    (relativeFppfSheaf f).obj.obj (op (variableHilbertTest f i.1 V)) :=
  variableHilbertPoint f i.1 hL V i.2 _ (𝟙 _)

/-- Restricting the chart's section is its actual translated parameter class. -/
theorem baseMarkedChartSection_map {U : Over (Spec (.of R))}
    (b : U ⟶ variableHilbertTest f i.1 V) :
    (relativeFppfSheaf f).obj.map b.op (baseMarkedChartSection f hL V i) =
      variableHilbertPoint f i.1 hL V i.2 U b := by
  simpa only [Category.comp_id, baseMarkedChartSection] using
    (variableHilbertPoint_natural f i.1 hL V i.2 b (𝟙 _)).symm

/-- The actual open intersection scheme for the two translated parameter charts. -/
def baseMarkedChartOverlap : Over (Spec (.of R)) :=
  baseMarkedHilbertIntersection f j.1 V _ j.2
    (variableHilbertBase f i.1 V) (baseMarkedChartSection f hL V i)

/-- The first overlap projection. -/
def baseMarkedChartOverlapLeft :
    baseMarkedChartOverlap f hL V i j ⟶ variableHilbertTest f i.1 V :=
  baseMarkedHilbertArrow f j.1 V _ j.2
    (variableHilbertBase f i.1 V) (baseMarkedChartSection f hL V i)

/-- The second overlap projection. -/
def baseMarkedChartOverlapRight :
    baseMarkedChartOverlap f hL V i j ⟶ variableHilbertTest f j.1 V :=
  baseMarkedHilbertParameter f hL j.1 V _ j.2
    (variableHilbertBase f i.1 V) (baseMarkedChartSection f hL V i)

instance baseMarkedChartOverlapLeft_isOpenImmersion :
    IsOpenImmersion (baseMarkedChartOverlapLeft f hL V i j).left :=
  baseMarkedHilbertArrow_isOpenImmersion _ _ _ _ _ _ _

instance baseMarkedChartOverlapLeft_mono :
    Mono (baseMarkedChartOverlapLeft f hL V i j) := Over.mono_of_mono_left _

/-- Both projections give exactly the same original Picard-sheaf section. -/
theorem baseMarkedChartOverlap_class :
    variableHilbertPoint f i.1 hL V i.2 _ (baseMarkedChartOverlapLeft f hL V i j) =
      variableHilbertPoint f j.1 hL V j.2 _
        (baseMarkedChartOverlapRight f hL V i j) := by
  rw [← baseMarkedChartSection_map]
  exact (baseMarkedHilbertParameter_class f hL j.1 V _ j.2
    (variableHilbertBase f i.1 V) (baseMarkedChartSection f hL V i)).symm

/-- The overlap remembers the same translation-base map on both sides. -/
@[reassoc]
theorem baseMarkedChartOverlap_base :
    baseMarkedChartOverlapRight f hL V i j ≫ variableHilbertBase f j.1 V =
      baseMarkedChartOverlapLeft f hL V i j ≫ variableHilbertBase f i.1 V :=
  baseMarkedHilbertParameter_base f hL j.1 V _ j.2 _ _

/-- Equal classes over the same base map factor through the actual open intersection. -/
theorem baseMarkedChartOverlap_lift {U : Over (Spec (.of R))}
    (a : U ⟶ variableHilbertTest f i.1 V) (b : U ⟶ variableHilbertTest f j.1 V)
    (hb : b ≫ variableHilbertBase f j.1 V = a ≫ variableHilbertBase f i.1 V)
    (hc : variableHilbertPoint f i.1 hL V i.2 U a =
      variableHilbertPoint f j.1 hL V j.2 U b) :
    ∃! k : U ⟶ baseMarkedChartOverlap f hL V i j,
      k ≫ baseMarkedChartOverlapLeft f hL V i j = a ∧
        k ≫ baseMarkedChartOverlapRight f hL V i j = b := by
  apply baseMarkedHilbertIntersection_lift f hL j.1 V _ j.2
    (variableHilbertBase f i.1 V) (baseMarkedChartSection f hL V i) a b hb
  rw [baseMarkedChartSection_map]
  exact hc.symm

/-- Exchange the two actual charts using the proved intersection universal property. -/
def baseMarkedChartOverlapSwap :
    baseMarkedChartOverlap f hL V i j ⟶ baseMarkedChartOverlap f hL V j i :=
  (baseMarkedChartOverlap_lift f hL V j i
    (baseMarkedChartOverlapRight f hL V i j) (baseMarkedChartOverlapLeft f hL V i j)
    (baseMarkedChartOverlap_base f hL V i j).symm
    (baseMarkedChartOverlap_class f hL V i j).symm).choose

@[reassoc]
lemma baseMarkedChartOverlapSwap_left :
    baseMarkedChartOverlapSwap f hL V i j ≫ baseMarkedChartOverlapLeft f hL V j i =
      baseMarkedChartOverlapRight f hL V i j :=
  (baseMarkedChartOverlap_lift f hL V j i _ _
    (baseMarkedChartOverlap_base f hL V i j).symm
    (baseMarkedChartOverlap_class f hL V i j).symm).choose_spec.1.1

@[reassoc]
lemma baseMarkedChartOverlapSwap_right :
    baseMarkedChartOverlapSwap f hL V i j ≫ baseMarkedChartOverlapRight f hL V j i =
      baseMarkedChartOverlapLeft f hL V i j :=
  (baseMarkedChartOverlap_lift f hL V j i _ _
    (baseMarkedChartOverlap_base f hL V i j).symm
    (baseMarkedChartOverlap_class f hL V i j).symm).choose_spec.1.2

/-- Exchanging the charts is an actual isomorphism of their intersection schemes. -/
def baseMarkedChartOverlapSymmetry :
    baseMarkedChartOverlap f hL V i j ≅ baseMarkedChartOverlap f hL V j i where
  hom := baseMarkedChartOverlapSwap f hL V i j
  inv := baseMarkedChartOverlapSwap f hL V j i
  hom_inv_id := by
    rw [← cancel_mono (baseMarkedChartOverlapLeft f hL V i j), Category.assoc,
      baseMarkedChartOverlapSwap_left, baseMarkedChartOverlapSwap_right,
      Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (baseMarkedChartOverlapLeft f hL V j i), Category.assoc,
      baseMarkedChartOverlapSwap_left, baseMarkedChartOverlapSwap_right,
      Category.id_comp]

/-- The second projection is open as well, via the constructed symmetry isomorphism. -/
instance baseMarkedChartOverlapRight_isOpenImmersion :
    IsOpenImmersion (baseMarkedChartOverlapRight f hL V i j).left := by
  have he := congrArg Over.Hom.left (baseMarkedChartOverlapSwap_left f hL V i j)
  rw [← he]
  change IsOpenImmersion ((baseMarkedChartOverlapSymmetry f hL V i j).hom.left ≫
    (baseMarkedChartOverlapLeft f hL V j i).left)
  infer_instance

end FLT.Mazur.HilbertChart
