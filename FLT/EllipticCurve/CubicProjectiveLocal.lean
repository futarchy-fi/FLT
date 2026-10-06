/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveAddition

/-! # Local projective addition on arbitrary input charts

The polynomial addition law yields genuine scheme morphisms on its ordinary
and infinity target domains, including neighborhoods of infinity plus a
finite point. The law still has base points on the diagonal. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Coordinate ring of an arbitrary pair of input charts. -/
abbrev ChartPairRing (b c : Bool) := Ring W b ⊗[R] Ring W c

/-- First projective input on a pair of charts. -/
def chartPairLeft (b c : Bool) : Fin 3 → ChartPairRing W b c :=
  chartPointCoords W b Algebra.TensorProduct.includeLeft

/-- Second projective input on a pair of charts. -/
def chartPairRight (b c : Bool) : Fin 3 → ChartPairRing W b c :=
  chartPointCoords W c Algebra.TensorProduct.includeRight

/-- Homogeneous addition coordinates on a pair of input charts. -/
def chartPairSum (b c : Bool) : Fin 3 → ChartPairRing W b c :=
  (W.map (algebraMap R (ChartPairRing W b c))).toProjective.addXYZ
    (chartPairLeft W b c) (chartPairRight W b c)

theorem chartPairSum_equation (b c : Bool) :
    (W.map (algebraMap R (ChartPairRing W b c))).toProjective.Equation
      (chartPairSum W b c) :=
  projective_addXYZ_equation _ (chartPointCoords_equation W b _)
    (chartPointCoords_equation W c _)

/-- The target coordinate that must be invertible for the selected chart. -/
def projectiveAdditionDenominator (b c d : Bool) : ChartPairRing W b c :=
  chartPairSum W b c (if d then 1 else 2)

/-- Coordinate ring of a domain of the projective addition law. -/
abbrev ProjectiveAdditionRing (b c d : Bool) :=
  Localization.Away (projectiveAdditionDenominator W b c d)

/-- Restriction to a domain of the projective addition law. -/
def projectiveAdditionRestriction (b c d : Bool) :
    ChartPairRing W b c →ₐ[R] ProjectiveAdditionRing W b c d :=
  IsScalarTower.toAlgHom R _ _

/-- Inverse of the selected target coordinate. -/
def projectiveAdditionInv (b c d : Bool) : ProjectiveAdditionRing W b c d :=
  IsLocalization.Away.invSelf (projectiveAdditionDenominator W b c d)

/-- Normalized output coordinates in the selected chart. -/
def projectiveAdditionCoords (b c d : Bool) : Fin 2 → ProjectiveAdditionRing W b c d :=
  ![projectiveAdditionRestriction W b c d (chartPairSum W b c 0) *
      projectiveAdditionInv W b c d,
    projectiveAdditionRestriction W b c d (chartPairSum W b c (if d then 2 else 1)) *
      projectiveAdditionInv W b c d]

theorem projectiveAdditionCoords_root (b c d : Bool) :
    aeval (projectiveAdditionCoords W b c d) (equation W d) = 0 := by
  have hp := chartPairSum_equation W b c
  have he : chartPairSum W b c =
      ![chartPairSum W b c 0, chartPairSum W b c 1, chartPairSum W b c 2] := by
    ext i
    fin_cases i <;> rfl
  rw [he] at hp
  cases d
  · exact affine_normalize_algHom W (projectiveAdditionRestriction W b c false) hp
      (IsLocalization.Away.mul_invSelf
        (S := ProjectiveAdditionRing W b c false) (projectiveAdditionDenominator W b c false))
  · exact infinity_normalize_algHom W (projectiveAdditionRestriction W b c true) hp
      (IsLocalization.Away.mul_invSelf
        (S := ProjectiveAdditionRing W b c true) (projectiveAdditionDenominator W b c true))

/-- Pullback of functions along a local projective addition morphism. -/
def projectiveAdditionSum (b c d : Bool) :
    Ring W d →ₐ[R] ProjectiveAdditionRing W b c d :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W d})
    (aeval (projectiveAdditionCoords W b c d)) (by
      change Ideal.span {equation W d} ≤
        RingHom.ker (aeval (projectiveAdditionCoords W b c d) :
          MvPolynomial (Fin 2) R →ₐ[R] ProjectiveAdditionRing W b c d).toRingHom
      rw [Ideal.span_le]
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact projectiveAdditionCoords_root W b c d)

@[simp] theorem projectiveAdditionSum_coord (b c d : Bool) (i : Fin 2) :
    projectiveAdditionSum W b c d (coord W d i) = projectiveAdditionCoords W b c d i := by
  change aeval _ (X i) = _
  simp

/-- Any pair of input charts embeds in the full cubic product. -/
def chartPairInclusion (b c : Bool) :
    pullback (chartToBase W b) (chartToBase W c) ⟶
      pullback (toBase W) (toBase W) :=
  pullback.map _ _ _ _ (sourceChart W b) (sourceChart W c) (𝟙 _) (by simp) (by simp)

instance chartPairInclusion_isOpenImmersion (b c : Bool) :
    IsOpenImmersion (chartPairInclusion W b c) := by
  unfold chartPairInclusion
  infer_instance

/-- The local projective addition domain is an actual open of the cubic product. -/
def projectiveAdditionInclusion (b c d : Bool) :
    Spec (.of (ProjectiveAdditionRing W b c d)) ⟶ pullback (toBase W) (toBase W) :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (ChartPairRing W b c) (ProjectiveAdditionRing W b c d))) ≫
    (pullbackSpecIso R (Ring W b) (Ring W c)).inv ≫ chartPairInclusion W b c

instance projectiveAdditionInclusion_isOpenImmersion (b c d : Bool) :
    IsOpenImmersion (projectiveAdditionInclusion W b c d) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ChartPairRing W b c) (ProjectiveAdditionRing W b c d)))) :=
    IsOpenImmersion.of_isLocalization (projectiveAdditionDenominator W b c d)
  unfold projectiveAdditionInclusion
  infer_instance

@[reassoc (attr := simp)] theorem projectiveAdditionInclusion_fst (b c d : Bool) :
    projectiveAdditionInclusion W b c d ≫ pullback.fst (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom
        ((projectiveAdditionRestriction W b c d).comp
          Algebra.TensorProduct.includeLeft).toRingHom) ≫
          sourceChart W b := by
  unfold projectiveAdditionInclusion chartPairInclusion chartToBase
  simp only [Category.assoc, pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)] theorem projectiveAdditionInclusion_snd (b c d : Bool) :
    projectiveAdditionInclusion W b c d ≫ pullback.snd (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom
        ((projectiveAdditionRestriction W b c d).comp
          Algebra.TensorProduct.includeRight).toRingHom) ≫
          sourceChart W c := by
  unfold projectiveAdditionInclusion chartPairInclusion chartToBase
  simp only [Category.assoc, pullback.map, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Addition on a normalized projective domain. -/
def projectiveAddition (b c d : Bool) :
    Spec (.of (ProjectiveAdditionRing W b c d)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (projectiveAdditionSum W b c d).toRingHom) ≫ sourceChart W d

@[reassoc (attr := simp)] theorem projectiveAddition_toBase (b c d : Bool) :
    projectiveAddition W b c d ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ProjectiveAdditionRing W b c d))) := by
  unfold projectiveAddition
  rw [Category.assoc, sourceChart_toBase]
  unfold chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (projectiveAdditionSum W b c d).comp_algebraMap

end WeierstrassCurve.CubicCharts
