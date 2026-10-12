/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOne
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationMono
public import FLT.Mazur.WeierstrassNodalDividedFamily
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# The actual depth-zero initial chart in the nonsplit nodal family

The scale-one comparison constructs the whole slope localization in the
residue-root gluing and then the original integral-root gluing. All family
coefficients come from the original nodal bounds, with no positive start depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth n : ℕ}
  (hbound : 2 * (0 + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hn : 0 < n)
  (j : ℕ) (hj : j ≤ n)
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "g3" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ
    (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "g4" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ
    (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "g6" => nodalDepthFamily_tangent_constant_zero
  hm hbound h3 h4 h6 hπ (Fin.mk 0 (Nat.zero_lt_succ n)) hn
local notation "e" => coefficientShearScaleOneEquiv W (π ^ 0)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r
  (nodalDepth_tangent_scale_zeroDepth (W := W) (π := π)) g3 g4 g6
  (residueTangentEquation_root W)
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "b" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))

/-- The complete depth-zero initial slope chart in the actual residue equation gluing. -/
def nodalDepthZeroInitialResidueChart : Spec (.of (SlopeOpen a)) ⟶
    coefficientShearGlued hπ data Q r j hj :=
  (E).hom ≫ coefficientShearGluedChart hπ data Q r j hj (.inl 2)

instance nodalDepthZeroInitialResidueChart_isOpenImmersion :
    IsOpenImmersion (nodalDepthZeroInitialResidueChart hπ hm hbound h3 h4 h6 hn j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Reconstruction is the entire original initial chart, with its actual tensor embedding. -/
@[reassoc] theorem nodalDepthZeroInitialResidueChart_reconstruction :
    nodalDepthZeroInitialResidueChart hπ hm hbound h3 h4 h6 hn j hj ≫
        (coefficientShearGluedIso hπ data Q r j hj).hom =
      (E).hom ≫ globalInitialCoefficientShearChart hπ data Q r j hj := by
  rw [nodalDepthZeroInitialResidueChart, Category.assoc, coefficientShearGluedIso_chart]
  rfl

/-- The complete localization keeps its original residue-root coefficient structure. -/
@[reassoc] theorem nodalDepthZeroInitialResidueChart_structure :
    nodalDepthZeroInitialResidueChart hπ hm hbound h3 h4 h6 hn j hj ≫
        coefficientShearGluedStructure hπ data Q r j hj =
      Spec.map (CommRingCat.ofHom (algebraMap Q (SlopeOpen a))) := by
  rw [nodalDepthZeroInitialResidueChart, Category.assoc, coefficientShearGluedChart_structure]
  exact terminalComponent_algebra_structure (e).toAlgHom

/-- The full depth-zero slope localization embeds in the original integral tangent model. -/
def nodalDepthZeroInitialChart : Spec (.of (SlopeOpen a)) ⟶
    coefficientShearGlued hπ data A rA j hj :=
  nodalDepthZeroInitialResidueChart hπ hm hbound h3 h4 h6 hn j hj ≫
    coefficientShearTangentSpecialization hπ data j hj

instance nodalDepthZeroInitialChart_mono :
    Mono (nodalDepthZeroInitialChart hπ hm hbound h3 h4 h6 hn j hj) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- Its integral coefficient map is the actual tangent-root specialization. -/
@[reassoc] theorem nodalDepthZeroInitialChart_structure :
    nodalDepthZeroInitialChart hπ hm hbound h3 h4 h6 hn j hj ≫
        coefficientShearGluedStructure hπ data A rA j hj =
      Spec.map (CommRingCat.ofHom (algebraMap Q (SlopeOpen a))) ≫ b := by
  rw [nodalDepthZeroInitialChart, Category.assoc, coefficientShearTangentSpecialization,
    coefficientShearSpecialization_structure, ← Category.assoc,
    nodalDepthZeroInitialResidueChart_structure]
  rfl

/-- Every original finite-model function is unchanged by the integral specialization. -/
@[reassoc] theorem nodalDepthZeroInitialChart_projection :
    nodalDepthZeroInitialChart hπ hm hbound h3 h4 h6 hn j hj ≫
        coefficientShearGluedProjection hπ data A rA j hj =
      nodalDepthZeroInitialResidueChart hπ hm hbound h3 h4 h6 hn j hj ≫
        coefficientShearGluedProjection hπ data Q r j hj := by
  rw [nodalDepthZeroInitialChart, Category.assoc, coefficientShearTangentSpecialization,
    coefficientShearSpecialization_projection]

end FLT.Mazur.WeierstrassDividedDepth
