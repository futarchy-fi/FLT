/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalAffineCompatibility
public import FLT.Mazur.AdicIdealPowerComparison

/-!
# Original scalar control of actual affine rank-tower representatives

The original affine coefficient ring is Noetherian, so the defining rank
ideal is finitely generated there. Whole scalar-fiber support then supplies
one cofinal shift controlling every difference of the actual representatives.
No finiteness of the invariant scalar ring or its correction cokernel is inferred.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance scalarCauchyOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarCauchyOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarCauchyOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha


local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb

omit [QuasiCompact p] [LocallyQuasiFinite p] in
/-- Finiteness of the rank ideal is proved in the original affine coefficient ring. -/
theorem rankStage_original_affine_noetherian : IsNoetherianRing Γ(X, U.1) :=
  IsLocallyNoetherian.component_noetherian U

variable {R₀ : Type} [CommRing R₀]
  [Algebra R₀ Γ((rankImageOpen (Over.mk p) n).toScheme,
    (rankStageOriginalAffineOpen (p := p) n b hb).1)]

/-- Actual core representatives are scalar Cauchy whenever the whole scalar fiber has this rank. -/
theorem rankStage_original_scalar_cauchy (J : Ideal R₀)
    (hsupport : PrimeSpectrum.zeroLocus (J.map (algebraMap R₀ Γ(X, U.1)) : Set Γ(X, U.1)) ⊆
      PrimeSpectrum.zeroLocus ((I).ideal U : Set Γ(X, U.1)))
    (h : ∀ k : ℕ, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ C k)
    (v : ∀ k : ℕ, rankStageCoreInvariants e n a ha k)
    (hc : ∀ k l (hkl : k ≤ l), rankStageCoreRestriction e n a ha hkl (v l) = v k)
    (w : ℕ → Γ(X, U.1))
    (hw : ∀ k, (I ^ (k + 1)).subschemeι.app U.1 (w k) =
      rankStageCoreAffineCoefficient e n a ha b hb k (h k) (v k).val) :
    ∃ c : ℕ, 0 < c ∧ ∀ m k l : ℕ, c * (m + 1) ≤ k + 1 → k ≤ l →
      w l - w k ∈ J ^ (m + 1) • (⊤ : Submodule R₀ Γ(X, U.1)) := by
  let _ := rankStage_original_affine_noetherian (p := p) n b hb
  obtain ⟨c, hcpos, hbound⟩ := AdicIdealPowerComparison.exists_power_bound_of_support J
    ((I).ideal U) ((I).ideal U).fg_of_isNoetherianRing hsupport
  refine ⟨c, hcpos, fun m k l hmk hkl ↦ ?_⟩
  have hd : w l - w k ∈ ((I).ideal U) ^ (k + 1) := by
    apply rankStage_original_affine_difference e n a ha b hb hkl (h k) (h l) (v l)
      (w l) (w k) (hw l)
    rw [hc]
    exact hw k
  exact AdicIdealPowerComparison.mem_scalar_power_of_mem_rank_power J ((I).ideal U)
    (hbound (m + 1)) (Ideal.pow_le_pow_right hmk hd)

end FLT.Mazur.EquivalenceRelationOrderedFrames
