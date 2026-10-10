/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalConicCoordinates
public import FLT.Mazur.WeierstrassDividedTerminalZeroConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureDescent

/-!
# Complete terminal and retained tensor intersections

The normalized conic incidence open presents the whole intersection of the
terminal node with the entire retained chart, at positive or zero depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "g" => globalSuccessiveTensorChart hπ data K j hj
local notation "T" => terminalNodeChart hπ data D (j + 1) hj (by omega) hk hp
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "q" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp
    (Data.b6 e) (Data.factor6 e))
local notation "s₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))

section Positive
variable (hk0 : 0 < start + j)
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => Iso.hom E ≫ PrincipalOpenTensor.inclusion K t

/-- The full positive retained chart meets the terminal node in its original conic open. -/
theorem terminalPositiveRetained_isPullback : IsPullback q b T g := by
  apply IsOpenImmersion.isPullback
  · rw [Category.assoc, residueConicBoundaryIso_inclusion_assoc]
    exact (terminalNodeConicCoordinates_chart hπ data D j hj hk0 hk hp).symm
  · apply TopologicalSpace.Opens.ext
    change g ⁻¹' Set.range T = Set.range b
    rw [terminalNodeChart_range, globalTensor_depthOverlap_preimage]
    symm
    change Set.range (fun z => PrincipalOpenTensor.inclusion K t ((E).hom z)) = _
    simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
      (E).hom.homeomorph.surjective.range_comp (PrincipalOpenTensor.inclusion K t)


/-- Two ordered puncture equations detect equality on the entire terminal overlap. -/
theorem terminalPositiveRetained_compatible_iff
    {Y : Scheme.{u}} (f : PolygonNodeBranches.node K ⟶ Y)
  (fRet : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
    (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) (ResidueField R))) ⟶ Y)
 :
    (pullback.fst T g ≫ f = pullback.snd T g ≫ fRet) ↔
      (s₁ ≫ q ≫ f = s₁ ≫ b ≫ fRet) ∧ (s₂ ≫ q ≫ f = s₂ ≫ b ≫ fRet) := by
  let H := terminalPositiveRetained_isPullback hπ data D j hj hk hp hk0
  have he : (pullback.fst T g ≫ f = pullback.snd T g ≫ fRet) ↔ q ≫ f = b ≫ fRet := by
    rw [← cancel_epi H.isoPullback.hom]
    simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
  rw [he]
  constructor
  · intro h
    exact ⟨congrArg (fun k => s₁ ≫ k) h, congrArg (fun k => s₂ ≫ k) h⟩
  · rintro ⟨h₁, h₂⟩
    exact residueConicPunctures_hom_ext D (start + j) hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
      (Data.factor6 e) hp _ _ h₁ h₂

end Positive

section Zero
variable (hk0 : start + j = 0)
local notation "E" => zeroResidueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => Iso.hom E ≫ PrincipalOpenTensor.inclusion K t

/-- The full zero retained chart meets the terminal node in its original conic open. -/
theorem terminalZeroRetained_isPullback : IsPullback q b T g := by
  apply IsOpenImmersion.isPullback
  · rw [Category.assoc, zeroResidueConicBoundaryIso_inclusion_assoc]
    exact (terminalNodeZeroConicCoordinates_chart hπ data D j hj hk0 hk hp).symm
  · apply TopologicalSpace.Opens.ext
    change g ⁻¹' Set.range T = Set.range b
    rw [terminalNodeChart_range, globalTensor_depthOverlap_preimage]
    symm
    change Set.range (fun z => PrincipalOpenTensor.inclusion K t ((E).hom z)) = _
    simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
      (E).hom.homeomorph.surjective.range_comp (PrincipalOpenTensor.inclusion K t)


/-- Two ordered puncture equations detect equality on the entire terminal overlap. -/
theorem terminalZeroRetained_compatible_iff
    {Y : Scheme.{u}} (f : PolygonNodeBranches.node K ⟶ Y)
  (fRet : Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
    (Data.b3 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b4 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) (ResidueField R))) ⟶ Y)
 :
    (pullback.fst T g ≫ f = pullback.snd T g ≫ fRet) ↔
      (s₁ ≫ q ≫ f = s₁ ≫ b ≫ fRet) ∧ (s₂ ≫ q ≫ f = s₂ ≫ b ≫ fRet) := by
  let H := terminalZeroRetained_isPullback hπ data D j hj hk hp hk0
  have he : (pullback.fst T g ≫ f = pullback.snd T g ≫ fRet) ↔ q ≫ f = b ≫ fRet := by
    rw [← cancel_epi H.isoPullback.hom]
    simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
  rw [he]
  constructor
  · intro h
    exact ⟨congrArg (fun k => s₁ ≫ k) h, congrArg (fun k => s₂ ≫ k) h⟩
  · rintro ⟨h₁, h₂⟩
    exact residueConicPunctures_hom_ext D (start + j) hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
      (Data.factor6 e) hp _ _ h₁ h₂

end Zero

end FLT.Mazur.WeierstrassDividedDepth
