/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonZeroTorusComparison
public import FLT.Mazur.PolygonGeneralizedCurve
public import FLT.Mazur.OneGonGlobalPushout

/-!
# The original pinched one-gon's smooth group in the closed cubic

The singleton split group is the torus with its original normalization coordinate.
Inverting this coordinate and using the actual closed smooth-group comparison
gives a group isomorphism to the complete family's original closed smooth group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.OneGonSmoothing
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]
local notation "G" => PolygonSplitGroup.model K 1
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "hp" => OneGonGlobalPushout.isPushout K (by decide)
local notation "E" => PolygonGeneralizedCurve.curve K 1 (by decide) p q hp
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The singleton split group is the original multiplicative group. -/
def originalOneGonGroupTorusIso : CommGrp.mk (G) ≅ CommGrp.mk (MultiplicativeGroupScheme.gm K) := by
  let e := coproductUniqueIso (fun _ : ZMod 1 => MultiplicativeGroupScheme.gm K)
  refine CommGrp.mkIso e ?_ ?_
  · change PolygonSplitGroup.identity K 1 ≫ e.hom = _
    simp only [PolygonSplitGroup.identity, PolygonSplitGroup.component, Category.assoc,
      e, ι_coproductUniqueIso_hom, eqToHom_refl, Category.comp_id]
  · apply PolygonSplitGroup.tensor_hom_ext
      (fun _ : ZMod 1 => MultiplicativeGroupScheme.gm K)
      (fun _ : ZMod 1 => MultiplicativeGroupScheme.gm K)
    intro i j
    change (PolygonSplitGroup.component K 1 i ⊗ₘ PolygonSplitGroup.component K 1 j) ≫
      μ[G] ≫ e.hom = _
    rw [PolygonSplitGroup.component_mul_assoc]
    simp only [PolygonSplitGroup.component, e, ι_coproductUniqueIso_hom,
      eqToHom_refl, Category.comp_id, tensorHom_comp_tensorHom_assoc,
      tensorHom_id, id_whiskerRight, Category.id_comp]

/-- The original component coordinate is retained by the singleton group isomorphism. -/
@[reassoc] theorem originalOneGonGroupTorusIso_component (i : ZMod 1) :
    PolygonSplitGroup.component K 1 i ≫
      (originalOneGonGroupTorusIso K).hom.hom.hom.hom = 𝟙 _ := by
  change Sigma.ι _ i ≫
    (coproductUniqueIso (fun _ : ZMod 1 => MultiplicativeGroupScheme.gm K)).hom = _
  simp

/-- Torus inversion preserves its commutative group law. -/
theorem originalTorusInversion_isMonHom : IsMonHom ι[MultiplicativeGroupScheme.gm K] := by
  constructor
  · have hi : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K) ≫
        ι[MultiplicativeGroupScheme.gm K] = 1 := by
      change (1 : 𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K)⁻¹ = 1
      exact inv_one
    simpa only [CategoryTheory.Hom.one_def,
      CartesianMonoidalCategory.toUnit_unique
        (CartesianMonoidalCategory.toUnit (𝟙_ (Over (Spec (.of K))))) (𝟙 _),
      Category.id_comp] using hi
  · rw [GrpObj.mul_inv_rev, IsCommMonObj.mul_comm]

/-- Torus inversion bundled as a group isomorphism. -/
def originalTorusInversion :
    CommGrp.mk (MultiplicativeGroupScheme.gm K) ≅
      CommGrp.mk (MultiplicativeGroupScheme.gm K) := by
  let _ := originalTorusInversion_isMonHom K
  exact CommGrp.mkIso' (asIso ι[MultiplicativeGroupScheme.gm K])

/-- The original singleton group maps to the closed smooth group with the correct coordinate. -/
def originalOneGonClosedGroupIso : CommGrp.mk (G) ≅ relativeTestGroup (t) (c) :=
  originalOneGonGroupTorusIso K ≪≫ originalTorusInversion K ≪≫
    (completeClosedGroupTorusIso K).symm

/-- The corrected group map retains inversion followed by the original closed comparison. -/
@[reassoc] theorem originalOneGonClosedGroupIso_component (i : ZMod 1) :
    PolygonSplitGroup.component K 1 i ≫
      (originalOneGonClosedGroupIso K).hom.hom.hom.hom =
    ι[MultiplicativeGroupScheme.gm K] ≫ (completeClosedGroupTorusOverIso K).inv := by
  change PolygonSplitGroup.component K 1 i ≫
    (originalOneGonGroupTorusIso K).hom.hom.hom.hom ≫ _ = _
  rw [originalOneGonGroupTorusIso_component_assoc]
  rfl

/-- The original generalized one-gon retains the original torus open immersion. -/
@[reassoc] theorem originalOneGon_inclusion_component (i : ZMod 1) :
    (PolygonSplitGroup.component K 1 i ≫ (E).inclusion).left = OneGonGluing.torus K := by
  let _ := polygon_lfp K 1 (by decide) (p) (q) (hp)
  change (PolygonSplitGroup.component K 1 i ≫
    PolygonActionSmooth.smoothMap K 1 (by decide) (p) (q) (hp)).left = _
  rw [PolygonActionSmooth.component_smoothMap,
    OneGonNormalization.componentι_normalizationOver]
  exact OneGonNormalization.torus_normalization K

end FLT.Mazur.OneGonSmoothing
