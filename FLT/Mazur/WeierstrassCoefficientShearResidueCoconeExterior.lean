/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCoconeLines
public import FLT.Mazur.WeierstrassResidueInfinityTensorCover
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeGluing

import all FLT.Mazur.WeierstrassCoefficientShearResidueInitial
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialCharts
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialCoconeDescent

import all FLT.Mazur.WeierstrassCoefficientShearResidueCoconeLines

/-!
# Full original exterior restriction of an arbitrary pinching cocone

The original complete affine line and shifted infinity tensor chart cover the
source. Their actual atlas restrictions therefore recover the entire exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 4) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 4) (by omega) C.inl C.inr C.condition i

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "D" => coefficientShearResidueAtlasCoconeMap
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "cover" => coefficientShearGluingCover hπ data Q r (s + 1) hs
local notation "G" => coefficientShearGluedIso hπ data Q r (s + 1) hs

local notation "M" => coefficientShearResidueGluedCoconeDesc
  hπ hm data s hs he hstart h3 h4 h6 h6next hc C
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "ini" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hstart
local notation "hr" => residueTangentEquation_root W
local notation "E" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a

/-- The entire original exterior component recovers the cocone's actual zero summand. -/
theorem coefficientShearResidueGluedCoconeDesc_exterior : E ≫ M = F 0 := by
  apply (cancel_epi (ProjectiveLine.slopeNormalizationIso a).hom).mp
  apply residueInfinityTensorParameter_hom_ext d (by dsimp; omega) hres a ha
  · rw [coefficientShearResidueExteriorLift_affine_assoc
      hπ data (s + 1) hs hstart hres hscale (ini).1 (ini).2 a]
    simp only [coefficientShearInitialLine, coefficientShearInitialFiber, Category.assoc]
    rw [coefficientShearResidueGluedCoconeDesc_chart,
      coefficientShearResidueAtlasCoconeMap_initial]
    simpa only [coefficientShearInitialEquationIso, Category.assoc] using
      coefficientShearResidueInitialCoconeDesc_incidence
        hπ hm data s hs (Nat.le_of_eq he) hstart h3 h4 h6 hc C
  · rw [coefficientShearResidueExteriorLift_infinityChart_assoc
      hπ data (s + 1) hs d (by dsimp; omega) hres a ha,
      coefficientShearResidueGluedCoconeDesc_chart,
      coefficientShearResidueAtlasCoconeMap_infinity,
      coefficientShearResidueInfinityCoconeDesc]

end FLT.Mazur.WeierstrassDividedDepth
