/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineScaling
public import FLT.Mazur.WeierstrassDividedFiniteLineBoundaryGeometry
public import FLT.Mazur.WeierstrassHorizontalBranchRestriction
public import FLT.Mazur.TensorOpenChartReparametrization

/-!
# Arithmetic Laurent branches and the original horizontal line lifts

Both punctures agree as scheme morphisms, with the signed inverse tangent
scale and the actual integral boundary transition kept explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PrincipalOpenTensor

/-- Normalizing the original tensor inclusion gives the actual principal-open inclusion. -/
@[reassoc] theorem normalized_tensorInclusion {A S R : Type u}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A] (x : A) :
    (TensorOpenChart.algebraIso (equiv (R := R) S x)).hom ≫
      tensorInclusion (R := R) S x = inclusion (R := R) S x := by
  rw [tensorInclusion_eq]
  exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.PrincipalOpenTensor
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "F" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "E" => TensorOpenChart.algebraIso (PrincipalOpenTensor.equiv (R := R) F x)
local notation "B" => PrincipalOpenTensor.transitionIso F x v (previousBoundaryEquiv hπ d e)
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "L" => WeierstrassSuccessiveX.residueLineToHorizontal D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N" => WeierstrassDilatation.residueNodeIso D (start + j) hk0 (by omega)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega)

/-- The transported full line lift restricts by its original divided contraction. -/
@[reassoc] theorem residueFiniteLineBoundary_inclusion
    (s : F) (hs : s * (s + residue R W.a₁) = 0) :
    Spec.map (CommRingCat.ofHom
        (residueFiniteLineBoundaryMap hπ data D j hj hk0 hk s hs).toRingHom) ≫
      PrincipalOpenTensor.inclusion F x =
        Spec.map (CommRingCat.ofHom (Polynomial.toLaurentAlg.comp
          (residueFiniteLineContraction hπ data D j hj hk0 hk s hs)).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (residueFiniteLineBoundaryMap_base hπ data D j hj hk0 hk s hs)

/-- The positive branch equals the full first line lift with inverse tangent scaling. -/
theorem residueHorizontalRight_line :
    WeierstrassDilatation.residueHorizontalRight D (start + j) hk0 (by omega)
      (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega) =
    Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (a)⁻¹).toRingHom) ≫
      L 0 (by simp) ≫ (B).hom ≫ (E).hom := by
  apply (cancel_mono (PrincipalOpenTensor.tensorInclusion F x)).mp
  rw [WeierstrassDilatation.residueHorizontalRight_inclusion]
  simp only [Category.assoc]
  rw [PrincipalOpenTensor.normalized_tensorInclusion]
  rw [← Category.assoc (L 0 (by simp)) (B).hom,
    residueFiniteLineBoundary_spec hπ data D j hj hk0 hk 0 (by simp),
    residueFiniteLineBoundary_inclusion]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun z => (residueFiniteFirstLine_scaling_tensor
    hπ data D j hj hk0 hk z).symm

/-- The negative branch equals the full opposite line lift with signed inverse scaling. -/
theorem residueHorizontalLeft_line :
    WeierstrassDilatation.residueHorizontalLeft D (start + j) hk0 (by omega)
      (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega) =
    Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
      L (-residue R W.a₁) (by simp) ≫ (B).hom ≫ (E).hom := by
  apply (cancel_mono (PrincipalOpenTensor.tensorInclusion F x)).mp
  rw [WeierstrassDilatation.residueHorizontalLeft_inclusion]
  simp only [Category.assoc]
  rw [PrincipalOpenTensor.normalized_tensorInclusion]
  rw [← Category.assoc (L (-residue R W.a₁) (by simp)) (B).hom,
    residueFiniteLineBoundary_spec hπ data D j hj hk0 hk (-residue R W.a₁) (by simp),
    residueFiniteLineBoundary_inclusion]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun z => (residueFiniteSecondLine_scaling_tensor
    hπ data D j hj hk0 hk z).symm

end FLT.Mazur.WeierstrassDividedDepth
