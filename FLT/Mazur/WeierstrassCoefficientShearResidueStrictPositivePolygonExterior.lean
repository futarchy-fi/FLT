/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositivePolygonIso
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositivePolygonIso
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLiftUnique

/-!
# The full polygon exterior retains the original split cubic

The pinching comparison has the actual coefficient specialization and cubic
contraction on the whole exterior. These equations characterize that map uniquely.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "pA" => coefficientShearGluedProjection hπ data A rA (s + 1) hs
local notation "sA" => coefficientShearGluedStructure hπ data A rA (s + 1) hs
local notation "q" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "I" => coefficientShearResidueStrictPositivePolygonIso
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "E" => PolygonCyclicAtlas.componentMap Q (2 * s + 5) (by omega) 0

/-- The entire polygon exterior specializes to the original ordered integral-target map. -/
@[reassoc] theorem coefficientShearResidueStrictPositivePolygonExterior_specialization :
    E ≫ (I).hom.left ≫ M = coefficientShearResidueOrderedExterior
      hπ data (s + 1) hs d (by dsimp; omega) hres a := by
  rw [coefficientShearResidueStrictPositivePolygonIso_exterior_assoc,
    coefficientShearResidueExteriorLift_specialization]

/-- The full original split cubic is retained, including both initial branches. -/
@[reassoc] theorem coefficientShearResidueStrictPositivePolygonExterior_toCurve :
    E ≫ (I).hom.left ≫ M ≫ pA ≫ finiteGlobalContraction hπ data (s + 1) hs =
      (ProjectiveLine.slopeNormalizationIso a).inv ≫
        originalResidueSplitCubic d (by dsimp; omega) hres := by
  rw [coefficientShearResidueStrictPositivePolygonExterior_specialization_assoc,
    coefficientShearResidueOrderedExterior_toCurve]

/-- The actual coefficient leg and complete cubic identify the polygon exterior uniquely. -/
theorem coefficientShearResidueStrictPositivePolygonExterior_unique
    (f : ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data A rA (s + 1) hs)
    (hf : f ≫ sA = ProjectiveLine.toBase Q ≫ q)
    (hcurve : f ≫ pA ≫ finiteGlobalContraction hπ data (s + 1) hs =
      (ProjectiveLine.slopeNormalizationIso a).inv ≫
        originalResidueSplitCubic d (by dsimp; omega) hres) :
    f = E ≫ (I).hom.left ≫ M := by
  rw [coefficientShearResidueStrictPositivePolygonExterior_specialization]
  exact coefficientShearResidueOrderedExterior_unique
    hπ data (s + 1) hs d (by dsimp; omega) hres a f hf hcurve

end FLT.Mazur.WeierstrassDividedDepth
