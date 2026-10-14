/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialLineProjection
public import FLT.Mazur.WeierstrassCoefficientShearRootChange

/-!
# Actual root translation on the full initial incidence line

Compare both incidence generators before taking spectra. Changing roots
translates the whole affine slope parameter, including both node markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r t : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "Lr" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr
local notation "Lt" => coefficientShearInitialLine hπ data S t j hj hs h3 h4 ht
local notation "cr" => originalShearInitialLineMap W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 hr
local notation "ct" => originalShearInitialLineMap W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S t hs h3 h4 ht
local notation "shift" => (aeval (X + C (r - t)) : S[X] →ₐ[S] S[X])
local notation "M" => coefficientShearRootChange hπ data S r t j hj

omit [IsDomain R] [IsBezout R] in
/-- Translating the slope preserves every original incidence function. -/
theorem coefficientShearInitialLineMap_rootChange :
    cr = ((shift).restrictScalars R).comp ct := by
  apply WeierstrassModificationX.hom_ext
  · simp only [AlgHom.comp_apply,
      originalShearInitialLineMap_t, map_zero]
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      originalShearInitialLineMap_v, map_add, aeval_X, aeval_C]
    rw [map_sub]
    change X + C r = (X + (C r - C t)) + C t
    ring

/-- The actual whole-model root change translates the full independent incidence line. -/
@[reassoc] theorem coefficientShearRootChange_initialLine :
    Lr ≫ (M).hom = Spec.map (CommRingCat.ofHom (shift).toRingHom) ≫ Lt := by
  apply (coefficientShearGlued_isPullback hπ data S t j hj).hom_ext
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearInitialLine_structure, Category.assoc,
      coefficientShearInitialLine_structure]
    exact (terminalComponent_algebra_structure shift).symm
  · rw [Category.assoc, coefficientShearRootChange_projection,
      coefficientShearInitialLine_projection, Category.assoc,
      coefficientShearInitialLine_projection, ← Spec.map_comp_assoc]
    congr 2
    exact congrArg (fun f => CommRingCat.ofHom (AlgHom.toRingHom f))
      (coefficientShearInitialLineMap_rootChange data S r t hs h3 h4 hr ht)

end FLT.Mazur.WeierstrassDividedDepth
