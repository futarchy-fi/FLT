/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialConicBoundaryAlgebra
public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection
public import FLT.Mazur.WeierstrassSuccessiveXResidueLineHorizontal

/-!
# Exact intersections of the full initial chart with the first residue lines

The horizontal line pullback and original tensor intersection retain the
whole Laurent parameter, with any chosen invertible reciprocal scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t₀" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u₀" => coord W (π ^ start) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "A" => PrincipalOpenTensor.transitionIso K x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d))
local notation "B" => PrincipalOpenTensor.transitionIso K x u₀ (previousBoundaryEquiv hπ d e)
local notation "H" => residueLineToHorizontal D start hstart hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

local notation "L" => residueSuccessiveLineImmersion D start hstart hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "p" => ProjectiveLine.overlapLeft K
variable (v : ResidueField R) (hv : v * (v + residue R W.a₁) = 0)
  (scale : (ResidueField R)ˣ)
local notation "ρ" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal scale)))

omit [IsBezout R] in
/-- The signed line pullback transported to the original common tensor boundary. -/
theorem initialLineCommonBoundary_isPullback :
    IsPullback (ρ ≫ H v hv ≫ (B).hom) (ρ ≫ p)
      ((B).inv ≫ PrincipalOpenTensor.inclusion K u₀) (L v hv) := by
  let I := Scheme.Spec.mapIso
    (PolygonScaledReciprocal.equiv scale).toRingEquiv.toCommRingCatIso.op
  apply (residueLineHorizontal_isPullback D start hstart hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) v hv).of_iso'
      I (B).symm (Iso.refl _) (Iso.refl _)
  · change ρ ≫ H v hv = (ρ ≫ H v hv ≫ (B).hom) ≫ (B).inv
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change ρ ≫ p = (ρ ≫ p) ≫ 𝟙 _
    rw [Category.comp_id]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

variable (r : ℕ) (hr : 1 + r ≤ n)
local notation "g" => globalInitialTensorChart hπ data K (1 + r) hr
local notation "gNext" => olderGlobalTensorChart hπ data K 0 h1 r hr

/-- The full initial chart meets a retained first line in exactly its signed puncture. -/
theorem initialRetainedLine_isPullback :
    IsPullback (ρ ≫ p)
      (ρ ≫ H v hv ≫ (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion K t₀)
      (L v hv ≫ gNext) g := by
  have T := (initialLineCommonBoundary_isPullback hπ data D h1 hstart hk v hv scale).flip
  have Q := T.paste_vert (initialRetainedGlobalTensor_isPullback hπ data K h1 r hr).flip
  simpa only [Category.assoc] using Q

end FLT.Mazur.WeierstrassDividedDepth
