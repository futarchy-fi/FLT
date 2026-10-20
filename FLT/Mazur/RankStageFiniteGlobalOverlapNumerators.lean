/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageGlobalBoundaryNumerators

/-!
# Global homogeneous numerators for every finite core overlap error

For independent lifts on the actual finite core cover, one constructed
exponent extends all overlap errors to full global invariant sections of the
rank stage. Each numerator vanishes on the whole original pulled boundary.
The overlap equation retains the exact error and the exact global norm power.
The exponent depends on the order; compatible numerators and an order-uniform
bound are not supplied by this finite construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
private theorem promote_numerator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r w : R) (v : S) {m N : ℕ} (hm : m ≤ N)
    (h : f w = f r ^ m * v) : f (r ^ (N - m) * w) = f r ^ N * v := by
  rw [map_mul, map_pow, h, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteNumOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteNumOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteNumOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (ha c) k) = ⊤)
  (J : A.IdealSheafData) (k : ℕ)
local notation "a" c:max => (c).val.1
local notation "hab" c:max d:max => rankStageProduct_domain n (a c) (a d) (ha c)
local notation "U" c:max d:max => rankStageCore e n (a c * a d) (hab c d) k
local notation "r" c:max d:max => rankStageNormParameter e n C ha hc (a c * a d) k
local notation "I" => rankStageBoundaryIdeal (p := p) n k J
local notation "B" => compatibleFunctions (rankStageFirst (p := p) n k) (rankStageSecond e n k)
attribute [local irreducible] rankStageCore rankStageNormParameter rankStageInvariantOverlapError

/-- One actual exponent clears all finite overlap errors into the full stage boundary kernel. -/
theorem exists_rankStage_finite_global_overlap_numerators
    (v : ∀ c : C, rankStageCoreInvariants e n (a c) (ha c) k) (t : Γ(J.subscheme, ⊤))
    (hv : ∀ c : C, (rankStageCoreBoundaryIdeal e n (a c) (ha c) J k).subschemeι.appTop
      (v c).val = (rankStageCoreOriginalBoundaryMap e n (a c) (ha c) J k).appTop t) :
    ∃ (N : ℕ) (w : C → C → B),
      (∀ c d, (I).subschemeι.appTop (w c d).val = 0) ∧
      ∀ c d, (U c d).ι.appTop (w c d).val = ((U c d).ι.appTop (r c d).val) ^ N *
        (rankStageInvariantOverlapError e n (a c) (a d) (ha c) (ha d) k (v c) (v d)).val := by
  classical
  have hex (x : C × C) := exists_rankStage_global_kernel_numerator e n C ha hc
    (a x.1 * a x.2) (hab x.1 x.2) J k
    (rankStageInvariantOverlapError e n (a x.1) (a x.2) (ha x.1) (ha x.2) k (v x.1) (v x.2))
    (rankStageInvariantOverlapError_boundary_zero e n (a x.1) (a x.2) (ha x.1) (ha x.2)
      J k (v x.1) (v x.2) t (hv x.1) (hv x.2))
  choose m z hz he using hex
  let N := Finset.univ.sup m
  have hm (x : C × C) : m x ≤ N := Finset.le_sup (Finset.mem_univ x)
  refine ⟨N, fun c d ↦ (r c d) ^ (N - m (c, d)) * z (c, d), ?_, ?_⟩
  · intro c d
    change (I).subschemeι.appTop
      ((r c d).val ^ (N - m (c, d)) * (z (c, d)).val) = 0
    rw [map_mul, hz (c, d), mul_zero]
  · intro c d
    change (U c d).ι.appTop ((r c d).val ^ (N - m (c, d)) * (z (c, d)).val) = _
    exact promote_numerator (U c d).ι.appTop.hom (r c d).val (z (c, d)).val
      (rankStageInvariantOverlapError e n (a c) (a d) (ha c) (ha d) k (v c) (v d)).val
      (hm (c, d)) (he (c, d))

end FLT.Mazur.EquivalenceRelationOrderedFrames
