/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroPinchingReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroPinchingColimit
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroSourceReflection

/-!
# Uniqueness and involutivity of the full start-zero pinching reflection

The actual normalization detects the entire reflected morphism. Its involution
therefore descends to the original target, alongside both reflected span legs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "C" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "c" => coefficientShearResidueZeroReflectionScale hm data s hs he h6next
local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc
local notation "J" => coefficientShearResidueZeroEqualityCycleNodes
  hπ hm data s hs he h3 h4 h6next hc
local notation "q" => Spec.map (CommRingCat.ofHom (f).toRingHom)

local notation "S" => PolygonPinching.semilinearScaledComponents (f).toRingHom c
local notation "D" => PolygonPinching.semilinearReflectionNodes (n := 2 * s + 2) (f).toRingHom
local notation "B" => PolygonPinching.semilinearReflectionBranches
  (n := 2 * s + 2) (f).toRingHom

/-- The full normalization formula uniquely determines the actual conjugation. -/
theorem coefficientShearResidueZeroReflection_unique
    (u : coefficientShearGlued hπ data
      (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
      (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶
      coefficientShearGlued hπ data
        (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
        (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs)
    (hu : (N).left ≫ u = S ≫ (N).left) : u = σ := by
  apply coefficientShearResidueZeroEqualityCycleCoproduct_hom_ext
    hπ hm data s hs he h3 h4 h6next hc
  exact hu.trans (coefficientShearResidueZeroEqualityCycleCoproduct_conjugation
    hπ hm data s hs he h3 h4 h6next hc).symm

include hm he h3 h4 h6next hc in
/-- The actual target reflection squares to the identity by full normalization detection. -/
@[reassoc] theorem coefficientShearResidueZeroReflection_involutive : σ ≫ σ = 𝟙 _ := by
  apply coefficientShearResidueZeroEqualityCycleCoproduct_hom_ext
    hπ hm data s hs he h3 h4 h6next hc
  rw [coefficientShearResidueZeroEqualityCycleCoproduct_conjugation_assoc,
    coefficientShearResidueZeroEqualityCycleCoproduct_conjugation,
    ← Category.assoc, coefficientShearResidueZeroSourceReflection_involutive,
    Category.id_comp]
  exact (Category.comp_id _).symm

omit [IsDomain R] [IsBezout R] in
/-- The original node reflection restores each coefficient point after two steps. -/
@[reassoc] theorem coefficientShearResidueZeroNodesReflection_involutive : D ≫ D = 𝟙 _ :=
  PolygonPinching.semilinearReflectionNodes_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

omit [IsDomain R] [IsBezout R] in
/-- The two original branch summands and their coefficient points are restored. -/
@[reassoc] theorem coefficientShearResidueZeroBranchesReflection_involutive : B ≫ B = 𝟙 _ :=
  PolygonPinching.semilinearReflectionBranches_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W))

end FLT.Mazur.WeierstrassDividedDepth
