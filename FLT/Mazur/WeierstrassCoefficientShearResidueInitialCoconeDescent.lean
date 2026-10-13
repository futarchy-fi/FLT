/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueInitialDescent
public import FLT.Mazur.PolygonCyclicPushout
import all FLT.Mazur.WeierstrassCoefficientShearResidueInitialDescent

/-!
# An arbitrary actual pinching cocone descends on the initial residue chart

No local compatibility hypotheses are supplied separately: they follow from
the equation of the original normalization-to-nodes span.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "ini" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d (by dsimp; omega) h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hstart
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "Z" => conicZeroAffineIso c g6
local notation "E" => coefficientShearInitialEquationIso data Q r (s + 1) hs
  hscale (ini).1 (ini).2 hr
local notation "p₁" => (conicFirstParameterIso (U).a₁ c hu).inv ≫
  conicFirstOpenImmersion (U).a₁ c
local notation "p₂" => (conicSecondParameterIso (U).a₁ c hu).inv ≫
  conicSecondOpenImmersion (U).a₁ c
local notation "ρ" => ProjectiveLine.endpointReversal Q
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 4)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 4) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 4) (by omega) C.inl C.inr C.condition i

/-- The actual initial coefficient equation receives any cocone on the original pinching span. -/
@[irreducible] def coefficientShearResidueInitialCoconeDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 2) ⟶ C.pt.left :=
  coefficientShearResidueInitialDesc hπ hm data s hs hk hstart h3 h4 h6 hc F w

/-- On the complete first branch the cocone keeps the required cyclic reversal. -/
theorem coefficientShearResidueInitialCoconeDesc_first :
    (Z).hom ≫ p₁ ≫ fiberConicImmersion (U).a₁ c ≫ (E).hom ≫
      coefficientShearResidueInitialCoconeDesc hπ hm data s hs hk hstart h3 h4 h6 hc C =
        ProjectiveLine.right Q ≫ F 1 := by
  rw [coefficientShearResidueInitialCoconeDesc, coefficientShearResidueInitialDesc_first]

/-- The opposite complete branch receives the actual last cyclic summand of the cocone. -/
theorem coefficientShearResidueInitialCoconeDesc_second :
    (Z).hom ≫ p₂ ≫ fiberConicImmersion (U).a₁ c ≫ (E).hom ≫
      coefficientShearResidueInitialCoconeDesc hπ hm data s hs hk hstart h3 h4 h6 hc C =
        ProjectiveLine.left Q ≫ F ⟨2 * s + 3, by omega⟩ := by
  rw [coefficientShearResidueInitialCoconeDesc, coefficientShearResidueInitialDesc_second]

/-- The entire initial incidence line receives the cocone's original exterior summand. -/
theorem coefficientShearResidueInitialCoconeDesc_incidence :
    fiberIncidenceImmersion (U).a₁ c ≫ (E).hom ≫
      coefficientShearResidueInitialCoconeDesc hπ hm data s hs hk hstart h3 h4 h6 hc C =
        ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueInitialCoconeDesc, coefficientShearResidueInitialDesc_incidence]

end FLT.Mazur.WeierstrassDividedDepth
