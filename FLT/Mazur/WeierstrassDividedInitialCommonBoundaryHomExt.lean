/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialCommonBoundaryAlgebra
public import FLT.Mazur.WeierstrassDividedFiniteLineBoundaryGeometry
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureDescent
public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection
public import FLT.Mazur.WeierstrassSuccessiveXResidueLineHorizontal

/-!
# The two signed punctures detect maps on the whole initial common boundary

The horizontal line pullback and original tensor intersection retain the
whole Laurent parameter, with any chosen invertible reciprocal scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
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

local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))

/-- Both signed punctures detect equality on the entire original common tensor boundary. -/
theorem initialCommonBoundary_hom_ext {Y : Scheme.{u}}
    (f g : Spec (.of (Localization.Away
      (WeierstrassDilatation.tensorX W (π ^ start)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) K))) ⟶ Y)
    (h₁ : (ρ₁ ≫ H 0 (by simp) ≫ (B).hom) ≫ f =
      (ρ₁ ≫ H 0 (by simp) ≫ (B).hom) ≫ g)
    (h₂ : (ρ₂ ≫ H (-a) (by simp) ≫ (B).hom) ≫ f =
      (ρ₂ ≫ H (-a) (by simp) ≫ (B).hom) ≫ g) : f = g := by
  cases start with
  | zero => omega
  | succ k =>
    let d₀ := data (Fin.mk 0 (Nat.zero_lt_succ n))
    let Q := Scheme.Spec.mapIso
      (residueDividedConicOpenEquiv D k (by omega)
        (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
        (Data.factor3 d₀) (Data.factor4 d₀)).toRingEquiv.toCommRingCatIso.op
    apply (cancel_epi Q.hom).mp
    apply residueConicPunctures_hom_ext D k (by omega)
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀)
      (Data.factor6 d₀) (by omega)
    · have E := congrArg (fun q => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom q)))
        (initialCommonFirstLine_localization hπ data D h1 (by omega))
      rw [lineSpec_comp, lineSpec_comp] at E
      rw [← residueFiniteLineBoundary_spec hπ data D 0 h1 (by omega) (by omega)
        0 (by simp)] at E
      change (_ ≫ Q.hom) ≫ f = (_ ≫ Q.hom) ≫ g
      erw [E]
      simpa only [Category.assoc] using h₁
    · have E := congrArg (fun q => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom q)))
        (initialCommonSecondLine_localization hπ data D h1 (by omega))
      rw [lineSpec_comp, lineSpec_comp] at E
      rw [← residueFiniteLineBoundary_spec hπ data D 0 h1 (by omega) (by omega)
        (-a) (by simp)] at E
      change (_ ≫ Q.hom) ≫ f = (_ ≫ Q.hom) ≫ g
      erw [E]
      simpa only [Category.assoc] using h₂

end FLT.Mazur.WeierstrassDividedDepth
