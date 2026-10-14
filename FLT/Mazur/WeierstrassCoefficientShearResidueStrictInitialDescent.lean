/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialProjectiveDescent
public import FLT.Mazur.WeierstrassCoefficientShearResidueInitialCharts
public import FLT.Mazur.PolygonCyclicPushout

/-!
# Odd cyclic descent on the actual positive-start initial chart

Cyclic endpoint data supplies both original attachment compatibilities.
The first branch is reversed back to its actual initial-component parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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
variable {Y : Scheme}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫ F i =
      ProjectiveLine.infinity (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) ≫
        F (PolygonPinching.next (by omega) i))

/-- Cyclic cocone data descends to the whole actual initial coefficient atlas equation. -/
@[irreducible] def coefficientShearResidueStrictInitialDesc :
    coefficientShearAtlasObject data Q r (s + 1) hs (.inl 2) ⟶ Y :=
  coefficientShearInitialProjectiveDesc data Q r (s + 1) hs hscale (ini).1 (ini).2 hr hu g6
    (ρ ≫ F 1) (F ⟨2 * s + 4, by omega⟩) (F 0)
    (by
      rw [ProjectiveLine.zero_endpointReversal_assoc]
      have hn : PolygonPinching.next (by omega) (0 : Fin (2 * s + 5)) = 1 := by
        apply Fin.ext
        change 1 % (2 * s + 5) = 1
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [hn] using (w 0).symm)
    (by
      have hn : PolygonPinching.next (by omega)
          (⟨2 * s + 4, by omega⟩ : Fin (2 * s + 5)) = 0 := by
        apply Fin.ext
        change (2 * s + 4 + 1) % (2 * s + 5) = 0
        rw [show 2 * s + 4 + 1 = 2 * s + 5 by omega, Nat.mod_self]
      simpa only [hn] using w ⟨2 * s + 4, by omega⟩)

/-- The full original first branch receives the correctly reversed cyclic map. -/
@[reassoc] theorem coefficientShearResidueStrictInitialDesc_first :
    (Z).hom ≫ p₁ ≫ fiberConicImmersion (U).a₁ c ≫ (E).hom ≫
      coefficientShearResidueStrictInitialDesc hπ hm data s hs hk hstart h3 h4 h6 hc F w =
        ProjectiveLine.right Q ≫ F 1 := by
  rw [coefficientShearResidueStrictInitialDesc, coefficientShearInitialProjectiveDesc_first,
    ProjectiveLine.left_endpointReversal_assoc]

/-- The entire opposite original branch receives the last cyclic component map. -/
@[reassoc] theorem coefficientShearResidueStrictInitialDesc_second :
    (Z).hom ≫ p₂ ≫ fiberConicImmersion (U).a₁ c ≫ (E).hom ≫
      coefficientShearResidueStrictInitialDesc hπ hm data s hs hk hstart h3 h4 h6 hc F w =
        ProjectiveLine.left Q ≫ F ⟨2 * s + 4, by omega⟩ := by
  rw [coefficientShearResidueStrictInitialDesc, coefficientShearInitialProjectiveDesc_second]

/-- The whole incidence line receives the original exterior map with its actual slope. -/
@[reassoc] theorem coefficientShearResidueStrictInitialDesc_incidence :
    fiberIncidenceImmersion (U).a₁ c ≫ (E).hom ≫
      coefficientShearResidueStrictInitialDesc hπ hm data s hs hk hstart h3 h4 h6 hc F w =
        ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueStrictInitialDesc, coefficientShearInitialProjectiveDesc_incidence]
  have he : Units.mk0 (U).a₁ (hu).ne_zero = a := Units.ext (ha).symm
  rw [he]

end FLT.Mazur.WeierstrassDividedDepth
