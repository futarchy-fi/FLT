/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialConicBoundaryAlgebra
public import FLT.Mazur.WeierstrassDividedInitialConicParameters

/-!
# The initial conic punctures retain their actual tensor boundary maps

Spectrum transports the full algebra identities before any contraction.
The two original conic punctures keep their signed reciprocal line lifts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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

/-- The localized initial map is the actual line lift and the two original transitions. -/
theorem initialLineBoundary_spec (r : K) (hr : r * (r + a) = 0) (scale : Kˣ) :
    Spec.map (CommRingCat.ofHom
      (initialLineBoundaryMap hπ data D h1 hstart hk r hr scale).toRingHom) =
    Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal scale).toRingHom) ≫
      H r hr ≫ (B).hom ≫ (A).inv := by
  rw [initialLineBoundaryMap, lineSpec_comp, lineSpec_comp]
  rw [← residueFiniteLineBoundary_spec hπ data D 0 h1 hstart hk r hr]
  simp only [Category.assoc]
  rfl

local notation "E" => residueFiberIso D start hstart (by omega)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "P₁" => conicPuncturedFirst (W.map (residue R)) c hc
local notation "P₂" => conicPuncturedSecond (W.map (residue R)) c hc
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))

/-- The first conic puncture is the original positive reciprocal tensor boundary map. -/
@[reassoc] theorem initialConicFirstLine_boundary_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom P₁)) ≫
      fiberConicImmersion a c ≫ (E).hom =
    ρ₁ ≫ H 0 (by simp) ≫ (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion K t₀ := by
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (initialConicFirstLine_algebra hπ data D h1 hstart hk)
  rw [lineSpec_comp, lineSpec_comp, lineSpec_comp] at h
  rw [initialLineBoundary_spec hπ data D h1 hstart hk] at h
  simp only [Category.assoc] at h
  convert h.symm using 1 <;> rfl

/-- The second conic puncture retains the negative reciprocal tensor boundary map. -/
@[reassoc] theorem initialConicSecondLine_boundary_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom P₂)) ≫
      fiberConicImmersion a c ≫ (E).hom =
    ρ₂ ≫ H (-a) (by simp) ≫ (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion K t₀ := by
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (initialConicSecondLine_algebra hπ data D h1 hstart hk)
  rw [lineSpec_comp, lineSpec_comp, lineSpec_comp] at h
  rw [initialLineBoundary_spec hπ data D h1 hstart hk] at h
  simp only [Category.assoc] at h
  convert h.symm using 1 <;> rfl

end FLT.Mazur.WeierstrassDividedDepth
