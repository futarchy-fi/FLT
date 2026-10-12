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
public import FLT.Mazur.WeierstrassNodalZeroInitialIntersection
public import FLT.Mazur.WeierstrassCoefficientShearInitialSlopeProjections

/-!
# Canonical slope projections of the actual depth-zero initial intersection

The whole original common boundary is the slope line. Its initial projection
is the identity and its retained projection is the original incidence-line inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048
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

local notation "I" => nodalDepthZeroInitialTensorIso hπ hm hbound h3 h4 h6 h1
local notation "J" => nodalDepthZeroRetainedTensorIso hπ hm hbound h3 h4 h6 h1
local notation "G" => coefficientShearGluedIso hπ data Q r (1 + m) ht
local notation "initial" => nodalDepthZeroInitialResidueChart
  hπ hm hbound h3 h4 h6 hn (1 + m) ht
local notation "retained" => nodalDepthZeroRetainedResidueChart
  hπ hm hbound h3 h4 h6 (1 + m) ht (by omega)

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

local notation "a" => WeierstrassCurve.a₁
  (rootShearCurve (W.map (algebraMap R Q)) r)
local notation "P" => SlopeOpen a
local notation "E" => coefficientShearInitialSlopeBoundaryEquiv hπ d e Q r gp g3e g4e hr

/-- The full original common boundary has its actual canonical slope parameter. -/
def nodalDepthZeroInitialBoundarySlopeIso :=
  Scheme.Spec.mapIso (E).toRingEquiv.toCommRingCatIso.op

local notation "K" => nodalDepthZeroInitialBoundarySlopeIso hπ hm hbound h3 h4 h6 h1
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Q) P))
local notation "l" => p ≫ fiberIncidenceImmersion a (algebraMap R Q (Data.b6 e))

omit [IsBezout R] in
/-- The initial projection of the entire original tensor boundary is the identity. -/
theorem nodalDepthZeroInitialBoundarySlope_initial : (K).hom ≫ f = 𝟙 _ := by
  apply (cancel_mono (I).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (AlgHom.congr_fun
    (coefficientShearInitialSlopeBoundary_initial hπ d e Q r gp g3e g4e hr g3 g4 g6))

omit [IsBezout R] in
/-- The retained projection is the whole punctured incidence line, with its canonical slope. -/
theorem nodalDepthZeroInitialBoundarySlope_retained : (K).hom ≫ g = l := by
  apply (cancel_mono (J).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ =
    Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (coefficientShearInitialSlopeBoundary_retained hπ d e Q r gp g3e g4e hr _).trans
    (tensorShearScaleOneHorizontalEquiv_base W (π ^ 0) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q r hs gp g3e g4e hr z)

/-- The canonical slope line is the full initial/first-retained residue intersection. -/
theorem nodalDepthZeroInitialSlopeResidue_isPullback :
    IsPullback (𝟙 _) l initial retained := by
  apply (nodalDepthZeroInitialResidue_isPullback hπ hm hbound h3 h4 h6 h1 m ht).of_iso'
    K (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa using nodalDepthZeroInitialBoundarySlope_initial hπ hm hbound h3 h4 h6 h1
  · simpa using nodalDepthZeroInitialBoundarySlope_retained hπ hm hbound h3 h4 h6 h1
  · simp
  · simp

/-- The same canonical slope square is the full intersection in the integral tangent model. -/
theorem nodalDepthZeroInitialSlope_isPullback :
    IsPullback (𝟙 _) l
      (nodalDepthZeroInitialChart hπ hm hbound h3 h4 h6 hn (1 + m) ht)
      (nodalDepthZeroRetainedChart hπ hm hbound h3 h4 h6 (1 + m) ht (by omega)) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (coefficientShearTangentSpecialization hπ data (1 + m) ht)
    (nodalDepthZeroInitialSlopeResidue_isPullback hπ hm hbound h3 h4 h6 h1 m ht).cone
    (nodalDepthZeroInitialSlopeResidue_isPullback hπ hm hbound h3 h4 h6 h1 m ht).isLimit)

end FLT.Mazur.WeierstrassDividedDepth
