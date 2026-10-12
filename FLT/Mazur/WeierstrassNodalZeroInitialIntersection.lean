/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalZeroInitialChart
import all FLT.Mazur.WeierstrassNodalZeroInitialChart
public import FLT.Mazur.WeierstrassNodalZeroRetainedChart
import all FLT.Mazur.WeierstrassNodalZeroRetainedChart
public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection

/-!
# The full depth-zero initial and first retained intersection

Transport the original full tensor-chart intersection through the actual
scale-one comparisons. The same cartesian square persists in the integral
tangent model, retaining both original principal-boundary projections.
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
  (h1 : 1 ≤ n) (m : ℕ) (ht : 1 + m ≤ n)
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "g3" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ
    (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "g4" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ
    (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "hn" => Nat.lt_of_lt_of_le Nat.zero_lt_one h1
local notation "g6" => nodalDepthFamily_tangent_constant_zero
  hm hbound h3 h4 h6 hπ (Fin.mk 0 (Nat.zero_lt_succ n)) hn
local notation "hs" => nodalDepth_tangent_scale_zeroDepth (W := W) (π := π)
local notation "hr" => residueTangentEquation_root W
local notation "ei" => coefficientShearScaleOneEquiv W (π ^ 0)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r hs g3 g4 g6 hr
local notation "gp" => residueTangentEquation_zero W π
  (Iff.mp (residue_eq_zero_iff π) (nodalDepth_residue_uniformizer hm))
local notation "g3e" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ
    (Fin.mk 1 (Nat.lt_succ_of_le h1)))
local notation "g4e" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ
    (Fin.mk 1 (Nat.lt_succ_of_le h1)))
local notation "ef" => coefficientShearScaleOneFiberEquiv W (π ^ 0) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q r hs gp g3e g4e hr

/-- The actual whole initial normal chart, with its original tensor algebra presentation. -/
def nodalDepthZeroInitialTensorIso :=
  (Scheme.Spec.mapIso (ei).toRingEquiv.toCommRingCatIso.op) ≪≫
    incidenceCoefficientShearIso W (π ^ 0) (Data.b3 d) (Data.b4 d) (Data.b6 d) Q r

/-- The whole first retained normal chart, with its original three-coordinate tensor algebra. -/
def nodalDepthZeroRetainedTensorIso :=
  (Scheme.Spec.mapIso (ef).toRingEquiv.toCommRingCatIso.op) ≪≫
    successiveCoefficientShearIso W (π ^ 0) π (Data.b3 e) (Data.b4 e) (Data.b6 e) Q r

local notation "I" => nodalDepthZeroInitialTensorIso hπ hm hbound h3 h4 h6 h1
local notation "J" => nodalDepthZeroRetainedTensorIso hπ hm hbound h3 h4 h6 h1
local notation "G" => coefficientShearGluedIso hπ data Q r (1 + m) ht
local notation "initial" => nodalDepthZeroInitialResidueChart
  hπ hm hbound h3 h4 h6 hn (1 + m) ht
local notation "retained" => nodalDepthZeroRetainedResidueChart
  hπ hm hbound h3 h4 h6 (1 + m) ht (by omega)

/-- The initial normal chart reconstructs the original whole tensor morphism. -/
@[reassoc] theorem nodalDepthZeroInitialTensorIso_chart :
    (I).hom ≫ globalInitialTensorChart hπ data Q (1 + m) ht = initial ≫ (G).hom := by
  rw [nodalDepthZeroInitialResidueChart_reconstruction]
  simp only [nodalDepthZeroInitialTensorIso, Iso.trans_hom, Category.assoc,
    globalInitialCoefficientShearChart]

/-- The first retained normal chart reconstructs its original tensor morphism at every depth. -/
@[reassoc] theorem nodalDepthZeroRetainedTensorIso_chart :
    (J).hom ≫ olderGlobalTensorChart hπ data Q 0 h1 m ht = retained ≫ (G).hom := by
  rw [nodalDepthZeroRetainedResidueChart_reconstruction,
    retainedCoefficientShearChart_original hπ data Q r 0 h1 m ht]
  simp only [nodalDepthZeroRetainedTensorIso, Iso.trans_hom, Category.assoc,
    olderGlobalCoefficientShearChart]

local notation "x" => WeierstrassDilatation.x W (π ^ 0)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ 0)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => coord W (π ^ 0) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (WeierstrassModificationX.overlapEquiv W (π ^ 0) (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso Q x u (previousBoundaryEquiv hπ d e)
local notation "f" => Iso.inv A ≫ PrincipalOpenTensor.inclusion Q t ≫ Iso.inv I
local notation "g" => Iso.inv B ≫ PrincipalOpenTensor.inclusion Q u ≫ Iso.inv J

/-- The original principal boundary is the complete intersection of both scale-one charts. -/
theorem nodalDepthZeroInitialResidue_isPullback : IsPullback f g initial retained := by
  apply (initialRetainedGlobalTensor_isPullback hπ data Q h1 m ht).of_iso'
    (Iso.refl _) I J G
  · simp only [Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  · exact nodalDepthZeroInitialTensorIso_chart hπ hm hbound h3 h4 h6 h1 m ht
  · exact nodalDepthZeroRetainedTensorIso_chart hπ hm hbound h3 h4 h6 h1 m ht

/-- The same full original boundary is the intersection inside the integral tangent model. -/
theorem nodalDepthZeroInitial_isPullback :
    IsPullback f g (nodalDepthZeroInitialChart hπ hm hbound h3 h4 h6 hn (1 + m) ht)
      (nodalDepthZeroRetainedChart hπ hm hbound h3 h4 h6 (1 + m) ht (by omega)) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (coefficientShearTangentSpecialization hπ data (1 + m) ht)
    (nodalDepthZeroInitialResidue_isPullback hπ hm hbound h3 h4 h6 h1 m ht).cone
    (nodalDepthZeroInitialResidue_isPullback hπ hm hbound h3 h4 h6 h1 m ht).isLimit)

end FLT.Mazur.WeierstrassDividedDepth
