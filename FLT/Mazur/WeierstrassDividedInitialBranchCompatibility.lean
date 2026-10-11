/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPunctureCompatibility
public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Initial tensor compatibility from full conic parameters and full lines

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
local notation "E" => residueFiberIso D start hstart (by omega)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "P₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicPuncturedFirst (W.map (residue R)) c hc)))
local notation "P₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicPuncturedSecond (W.map (residue R)) c hc)))
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
variable (r : ℕ) (hr : 1 + r ≤ n)
local notation "g" => globalInitialTensorChart hπ data K (1 + r) hr
local notation "gNext" => olderGlobalTensorChart hπ data K 0 h1 r hr
variable {Y : Scheme.{u}}
  (f : Spec (.of (WeierstrassModificationX.ScalarExtension W (π ^ start)
    (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩))
    (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩))
    (Data.b6 (data ⟨0, Nat.zero_lt_succ n⟩)) (ResidueField R))) ⟶ Y)
  (fNext : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ start) π
    (Data.b3 (data ⟨1, Nat.lt_succ_of_le h1⟩))
    (Data.b4 (data ⟨1, Nat.lt_succ_of_le h1⟩))
    (Data.b6 (data ⟨1, Nat.lt_succ_of_le h1⟩)) (ResidueField R))) ⟶ Y)

local notation "ha" => D.a₁_unit.map (residue R)
local notation "C₁" => Iso.hom (conicZeroAffineIso c hc) ≫
  Iso.inv (conicFirstParameterIso a c ha) ≫ conicFirstOpenImmersion a c ≫
    fiberConicImmersion a c ≫ Iso.hom E
local notation "C₂" => Iso.hom (conicZeroAffineIso c hc) ≫
  Iso.inv (conicSecondParameterIso a c ha) ≫ conicSecondOpenImmersion a c ≫
    fiberConicImmersion a c ≫ Iso.hom E

/-- Full parameter restrictions preserve both projective orientations on the whole overlap. -/
theorem initialRetained_compatible_of_branch_restrictions
    (F₁ F₂ : ProjectiveLine.scheme K ⟶ Y)
    (h₁ : C₁ ≫ f = ProjectiveLine.right K ≫ F₁)
    (h₂ : C₂ ≫ f = ProjectiveLine.left K ≫ F₂)
    (h₃ : ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ L 0 (by simp) ≫ fNext =
      ProjectiveLine.left K ≫ F₁)
    (h₄ : ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ L (-a) (by simp) ≫ fNext =
      ProjectiveLine.right K ≫ F₂) :
    pullback.fst g gNext ≫ f = pullback.snd g gNext ≫ fNext := by
  apply initialRetained_compatible_of_punctures hπ data D h1 hstart hk r hr f fNext
  · rw [conicPuncturedFirst_spec c hc (W.map (residue R)) ha]
    rw [← conicZeroAffineIso_puncture c hc]
    simp only [Category.assoc, WeierstrassCurve.map_a₁] at h₁ ⊢
    rw [h₁, ProjectiveLine.scaledReciprocal_overlap_assoc, h₃,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => q ≫ F₁) (ProjectiveLine.endpointReversal_overlap K)
  · rw [conicPuncturedSecond_spec c hc (W.map (residue R)) ha]
    rw [← conicZeroAffineIso_puncture c hc]
    simp only [Category.assoc, WeierstrassCurve.map_a₁] at h₂ ⊢
    rw [h₂, ProjectiveLine.scaledReciprocal_overlap_assoc, h₄,
      ← Category.assoc, ← Category.assoc]
    exact congrArg (fun q => q ≫ F₂) (ProjectiveLine.overlap_condition K)

end FLT.Mazur.WeierstrassDividedDepth
