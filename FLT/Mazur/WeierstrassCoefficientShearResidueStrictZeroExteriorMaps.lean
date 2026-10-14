/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps

/-!
# The initial and infinity charts of a strict start-zero cocone

Both charts map through the original exterior summand. The initial equation is
its whole slope localization; the infinity equation uses the data at depth one.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)

local notation "gc" => coefficientShearResidueZeroInitial_coefficients hπ hm data s hs
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "eqv" => coefficientShearScaleOneEquiv W (π ^ (0 + 0))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r (by simp)
  (gc).1 (gc).2.1 (gc).2.2 (residueTangentEquation_root W)

local notation "E" => coefficientShearResidueZeroInitialIso hπ hm data s hs

variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 3)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 3) C.inl

/-- The complete initial equation maps through the sole original exterior component. -/
@[irreducible] def coefficientShearResidueStrictZeroInitialCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 2) ⟶ C.pt.left :=
  (E).inv ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial Q) (SlopeOpen (U).a₁))) ≫ ProjectiveLine.left Q ≫
      (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0

/-- Its full slope localization has the prescribed original exterior map. -/
theorem coefficientShearResidueStrictZeroInitialCoconeDesc_slope :
    (E).hom ≫ coefficientShearResidueStrictZeroInitialCoconeDesc
      hπ hm data s hs h3 h4 hc C =
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Q) (SlopeOpen (U).a₁))) ≫
          ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueStrictZeroInitialCoconeDesc, Iso.hom_inv_id_assoc]

/-- The entire infinity chart also maps through the original exterior, at every chain length. -/
@[irreducible] def coefficientShearResidueStrictZeroInfinityCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 0) ⟶ C.pt.left :=
  residueInfinityTensorParameter e (by simp) (nodalDepth_residue_uniformizer hm) a ha ≫
    (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0

omit [IsDomain R] in
/-- The whole infinity map retains the coefficient field structure. -/
theorem coefficientShearResidueStrictZeroInfinityCoconeDesc_structure :
    coefficientShearResidueStrictZeroInfinityCoconeDesc hm data s hs h3 h4 hc C ≫ C.pt.hom =
      coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0) := by
  have hf : F 0 ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 3) 0 ≫ C.inl).w
  rw [coefficientShearResidueStrictZeroInfinityCoconeDesc]
  simp only [Category.assoc]
  rw [hf, ProjectiveLine.slopeNormalizationIso_base, residueInfinityTensorParameter_structure]
  rfl

/-- The whole initial map retains the coefficient field structure. -/
theorem coefficientShearResidueStrictZeroInitialCoconeDesc_structure :
    coefficientShearResidueStrictZeroInitialCoconeDesc hπ hm data s hs h3 h4 hc C ≫ C.pt.hom =
      coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 2) := by
  have hf : F 0 ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 3) 0 ≫ C.inl).w
  apply (cancel_epi (E).hom).mp
  rw [← Category.assoc, coefficientShearResidueStrictZeroInitialCoconeDesc_slope]
  simp only [Category.assoc]
  rw [hf, ProjectiveLine.slopeNormalizationIso_base, ProjectiveLine.left_toBase]
  change Spec.map _ ≫ Spec.map _ = (E).hom ≫ Spec.map _
  rw [← Spec.map_comp]
  exact (terminalComponent_algebra_structure (eqv).toAlgHom).symm

end FLT.Mazur.WeierstrassDividedDepth
