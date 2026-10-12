/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOne
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationMono
public import FLT.Mazur.WeierstrassNodalDividedFamily
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# The actual first retained chart of a depth-zero nonsplit nodal family

The full scale-one retained equation becomes the incidence-conic equation.
The residue comparison and its integral tangent specialization keep the
whole original chart and both of its original projection maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth n : ℕ}
  (hbound : 2 * (0 + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (j : ℕ) (hj : j ≤ n) (hpos : 0 < j)
include hpos
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk 1 (by omega))
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "g3" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk 1 (by omega)))
local notation "g4" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk 1 (by omega)))
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "gp" => residueTangentEquation_zero W π
  (Iff.mp (residue_eq_zero_iff π) (nodalDepth_residue_uniformizer hm))
local notation "e" => coefficientShearScaleOneFiberEquiv W (π ^ 0) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r
  (nodalDepth_tangent_scale_zeroDepth (W := W) (π := π)) gp g3 g4
  (residueTangentEquation_root W)
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "b" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))

/-- The complete first retained incidence-conic chart in the actual residue equation gluing. -/
def nodalDepthZeroRetainedResidueChart : Spec (.of (FiberCoordinate a c)) ⟶
    coefficientShearGlued hπ data Q r j hj :=
  (E).hom ≫ coefficientShearGluedChart hπ data Q r j hj (.inr ⟨0, hpos⟩)

instance nodalDepthZeroRetainedResidueChart_isOpenImmersion :
    IsOpenImmersion (nodalDepthZeroRetainedResidueChart hπ hm hbound h3 h4 h6 j hj hpos) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Reconstruction is the entire original first retained chart, with its actual tensor embedding. -/
@[reassoc] theorem nodalDepthZeroRetainedResidueChart_reconstruction :
    nodalDepthZeroRetainedResidueChart hπ hm hbound h3 h4 h6 j hj hpos ≫
        (coefficientShearGluedIso hπ data Q r j hj).hom =
      (E).hom ≫ retainedCoefficientShearChart hπ data Q r j hj 0 hpos := by
  rw [nodalDepthZeroRetainedResidueChart, Category.assoc, coefficientShearGluedIso_chart]
  rfl

/-- The complete incidence-conic equation keeps its original residue-root coefficient structure. -/
@[reassoc] theorem nodalDepthZeroRetainedResidueChart_structure :
    nodalDepthZeroRetainedResidueChart hπ hm hbound h3 h4 h6 j hj hpos ≫
        coefficientShearGluedStructure hπ data Q r j hj =
      Spec.map (CommRingCat.ofHom (algebraMap Q (FiberCoordinate a c))) := by
  rw [nodalDepthZeroRetainedResidueChart, Category.assoc, coefficientShearGluedChart_structure]
  exact terminalComponent_algebra_structure (e).toAlgHom

/-- The full first retained equation embeds in the original integral tangent model. -/
def nodalDepthZeroRetainedChart : Spec (.of (FiberCoordinate a c)) ⟶
    coefficientShearGlued hπ data A rA j hj :=
  nodalDepthZeroRetainedResidueChart hπ hm hbound h3 h4 h6 j hj hpos ≫
    coefficientShearTangentSpecialization hπ data j hj

instance nodalDepthZeroRetainedChart_mono :
    Mono (nodalDepthZeroRetainedChart hπ hm hbound h3 h4 h6 j hj hpos) :=
  inferInstanceAs (Mono (_ ≫ _))

/-- Its integral coefficient map is the actual tangent-root specialization. -/
@[reassoc] theorem nodalDepthZeroRetainedChart_structure :
    nodalDepthZeroRetainedChart hπ hm hbound h3 h4 h6 j hj hpos ≫
        coefficientShearGluedStructure hπ data A rA j hj =
      Spec.map (CommRingCat.ofHom (algebraMap Q (FiberCoordinate a c))) ≫ b := by
  rw [nodalDepthZeroRetainedChart, Category.assoc, coefficientShearTangentSpecialization,
    coefficientShearSpecialization_structure, ← Category.assoc,
    nodalDepthZeroRetainedResidueChart_structure]
  rfl

/-- Every original finite-model function is unchanged by the integral specialization. -/
@[reassoc] theorem nodalDepthZeroRetainedChart_projection :
    nodalDepthZeroRetainedChart hπ hm hbound h3 h4 h6 j hj hpos ≫
        coefficientShearGluedProjection hπ data A rA j hj =
      nodalDepthZeroRetainedResidueChart hπ hm hbound h3 h4 h6 j hj hpos ≫
        coefficientShearGluedProjection hπ data Q r j hj := by
  rw [nodalDepthZeroRetainedChart, Category.assoc, coefficientShearTangentSpecialization,
    coefficientShearSpecialization_projection]

end FLT.Mazur.WeierstrassDividedDepth
