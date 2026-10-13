/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOne
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorInfinity
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# The full initial and infinity charts of a start-zero cocone

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

include hπ hm s hs in
/-- The original scale-zero coefficients vanish because the next divided stage exists. -/
theorem coefficientShearResidueZeroInitial_coefficients :
    algebraMap R Q (d).b3 = 0 ∧ algebraMap R Q (d).b4 = 0 ∧
      algebraMap R Q (d).b6 = 0 := by
  constructor
  · rw [factor3_step hπ d e, map_mul, hp, zero_mul]
  constructor
  · rw [factor4_step hπ d e, map_mul, hp, zero_mul]
  · rw [factor6_step hπ d e, map_mul, map_pow, hp, zero_pow (by decide : 2 ≠ 0),
      zero_mul]
local notation "gc" => coefficientShearResidueZeroInitial_coefficients hπ hm data s hs
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "eqv" => coefficientShearScaleOneEquiv W (π ^ (0 + 0))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r (by simp)
  (gc).1 (gc).2.1 (gc).2.2 (residueTangentEquation_root W)

/-- The entire original initial equation is isomorphic to the full punctured slope line. -/
def coefficientShearResidueZeroInitialIso :
    Spec (.of (SlopeOpen (U).a₁)) ≅
      coefficientShearAtlasObject data Q r (s + 1) hs (.inl 2) :=
  by
    change Spec (.of (SlopeOpen (U).a₁)) ≅ Spec (.of (Coordinate U
      (algebraMap R Q (π ^ 0)) (algebraMap R Q (Data.b3 d))
      (algebraMap R Q (Data.b4 d) - r * algebraMap R Q (Data.b3 d))
      (algebraMap R Q (Data.b6 d))))
    let f := eqv
    let iso := Scheme.Spec.mapIso f.toRingEquiv.toCommRingCatIso.op
    exact iso
local notation "E" => coefficientShearResidueZeroInitialIso hπ hm data s hs

variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl

/-- The complete initial equation maps through the sole original exterior component. -/
@[irreducible] def coefficientShearResidueZeroInitialCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 2) ⟶ C.pt.left :=
  (E).inv ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial Q) (SlopeOpen (U).a₁))) ≫ ProjectiveLine.left Q ≫
      (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0

/-- Its full slope localization has the prescribed original exterior map. -/
theorem coefficientShearResidueZeroInitialCoconeDesc_slope :
    (E).hom ≫ coefficientShearResidueZeroInitialCoconeDesc
      hπ hm data s hs h3 h4 hc C =
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Q) (SlopeOpen (U).a₁))) ≫
          ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueZeroInitialCoconeDesc, Iso.hom_inv_id_assoc]

/-- The entire infinity chart also maps through the original exterior, at every chain length. -/
@[irreducible] def coefficientShearResidueZeroInfinityCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 0) ⟶ C.pt.left :=
  residueInfinityTensorParameter e (by simp) (nodalDepth_residue_uniformizer hm) a ha ≫
    (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0

omit [IsDomain R] in
/-- The whole infinity map retains the coefficient field structure. -/
theorem coefficientShearResidueZeroInfinityCoconeDesc_structure :
    coefficientShearResidueZeroInfinityCoconeDesc hm data s hs h3 h4 hc C ≫ C.pt.hom =
      coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0) := by
  have hf : F 0 ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 2) 0 ≫ C.inl).w
  rw [coefficientShearResidueZeroInfinityCoconeDesc]
  simp only [Category.assoc]
  rw [hf, ProjectiveLine.slopeNormalizationIso_base, residueInfinityTensorParameter_structure]
  rfl

/-- The whole initial map retains the coefficient field structure. -/
theorem coefficientShearResidueZeroInitialCoconeDesc_structure :
    coefficientShearResidueZeroInitialCoconeDesc hπ hm data s hs h3 h4 hc C ≫ C.pt.hom =
      coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 2) := by
  have hf : F 0 ≫ C.pt.hom = ProjectiveLine.toBase Q :=
    (PolygonPinching.componentι Q (2 * s + 2) 0 ≫ C.inl).w
  apply (cancel_epi (E).hom).mp
  rw [← Category.assoc, coefficientShearResidueZeroInitialCoconeDesc_slope]
  simp only [Category.assoc]
  rw [hf, ProjectiveLine.slopeNormalizationIso_base, ProjectiveLine.left_toBase]
  change Spec.map _ ≫ Spec.map _ = (E).hom ≫ Spec.map _
  rw [← Spec.map_comp]
  exact (terminalComponent_algebra_structure (eqv).toAlgHom).symm

end FLT.Mazur.WeierstrassDividedDepth
