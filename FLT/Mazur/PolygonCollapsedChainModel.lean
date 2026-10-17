/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedFiberReduced
public import FLT.Mazur.PolygonOmittedComponentCover

/-!
# The global reduced union model of the collapsed chain

Construct the reduced closed union of the omitted original projective lines.
The full fiber ideal, proved radical separately, identifies this model with the
actual Cartesian fiber. The comparison retains all original component maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainModel
open PolygonCyclicAtlas PolygonOneGonContraction PolygonCollapsedFiberReduced
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "p" => normalization K n h
local notation "q" => nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "F" => fiberIdeal K n (by omega) p q hp i
local notation "c" => Over.Hom.left (contraction K n (by omega) p q hp i)
local notation "t" => Over.Hom.left (targetNode K)

/-- The vanishing ideal of the finite union of the original omitted complete components. -/
def chainIdeal : (PolygonCyclicAtlas.scheme K n h).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨⋃ j : {j : Fin n // j ≠ i}, Set.range (componentMap K n h j.val),
      PolygonOmittedComponentCover.omittedUnion_isClosed K n h i⟩

/-- The actual global reduced closed union model, with its original embedding. -/
def chain : Scheme := (chainIdeal K n h i).subscheme

/-- The full collapsed fiber ideal equals the independently specified reduced union ideal. -/
theorem fiberIdeal_eq_chainIdeal : F = chainIdeal K n h i := by
  rw [← fiberIdeal_radical K n h i,
    ← Scheme.IdealSheafData.vanishingIdeal_support (I := F)]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  exact TopologicalSpace.Closeds.ext (PolygonOmittedComponentCover.support_eq K n h i)

/-- The Cartesian collapsed fiber is isomorphic to the global reduced union model. -/
def chainFiberIso : pullback (c) (t) ≅ chain K n h i :=
  fiberIso K n h i ≪≫
    BaseAdicThickening.subschemeCongr (fiberIdeal_eq_chainIdeal K n h i)

/-- This is an isomorphism over the original polygon, not just a support identification. -/
@[reassoc] theorem chainFiberIso_hom_ι :
    (chainFiberIso K n h i).hom ≫ (chainIdeal K n h i).subschemeι =
      pullback.fst (c) (t) := by
  simp only [chainFiberIso, Iso.trans_hom, Category.assoc,
    BaseAdicThickening.subschemeCongr_hom_ι, fiberIso_hom_ι]

/-- The constructed global union model is reduced. -/
instance chain_isReduced : IsReduced (chain K n h i) :=
  isReduced_of_isOpenImmersion (chainFiberIso K n h i).inv

/-- Each omitted original projective line maps to the constructed global chain. -/
def component {j : Fin n} (hj : j ≠ i) : ProjectiveLine.scheme K ⟶ chain K n h i :=
  omittedFiberMap K n (by omega) p q hp i hj ≫ (chainFiberIso K n h i).hom

/-- The chain component map retains the actual normalization map into the polygon. -/
@[reassoc] theorem component_ι {j : Fin n} (hj : j ≠ i) :
    component K n h i hj ≫ (chainIdeal K n h i).subschemeι = componentMap K n h j := by
  rw [component, Category.assoc, chainFiberIso_hom_ι, omittedFiberMap_fst,
    componentι_normalization]
  rfl

/-- The original adjacent endpoints are identified in the global chain as scheme morphisms. -/
theorem component_endpoints (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    ProjectiveLine.zero K ≫ component K n h i hj =
      ProjectiveLine.infinity K ≫ component K n h i hs := by
  apply (cancel_mono (chainIdeal K n h i).subschemeι).mp
  rw [Category.assoc, Category.assoc, component_ι, component_ι,
    zero_componentMap, infinity_componentMap, Equiv.symm_apply_apply]

end FLT.Mazur.PolygonCollapsedChainModel
