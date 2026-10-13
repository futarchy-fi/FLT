/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialEquationDescent
public import FLT.Mazur.WeierstrassIncidenceShearInfinitySlope
public import FLT.Mazur.WeierstrassDividedInitialTensorInfinityIntersection

/-!
# The full original initial and infinity atlas pullback after root shear

The entire shifted slope localization is the actual atlas intersection.
Both projections retain their original tensor and coefficient equation maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (d).b6
local notation "E" => coefficientShearInitialEquationIso data S r j hj hs h3 h4 hr
local notation "ci" => incidenceCoefficientShearIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r
local notation "P" => Localization.Away
  (slopePolynomial a * (Polynomial.X + Polynomial.C r))
local notation "L" => tensorShearInitialInfinitySlopeIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r hs h3 h4 hr
local notation "e" => tensorShearNormalEquiv W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r hs h3 h4 hr
local notation "N" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial S) P))
local notation "A" => coefficientShearAtlasMap hπ data S r j hj

omit [IsDomain R] [IsBezout R] in
/-- The full tensor normal comparison gives the actual coefficient equation after inverse shear. -/
@[reassoc] theorem coefficientShearInitialEquationIso_tensor_normal :
    (N).hom ≫ (ci).inv = (E).hom := by
  apply (cancel_mono (ci).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The entire original shifted slope boundary maps to the full infinity atlas object. -/
def coefficientShearInitialInfinitySlope :
    Spec (.of P) ⟶ coefficientShearAtlasObject data S r j hj (.inl 0) :=
  (L).hom ≫ initialGlobalYToInfinity hπ data S j hj
local notation "b" => coefficientShearInitialInfinitySlope
  hπ data S r j hj hs h3 h4 hr

/-- The complete shifted slope is the whole original initial/infinity atlas pullback. -/
theorem coefficientShearInitialInfinity_isPullback :
    IsPullback b (p ≫ fiberIncidenceImmersion a c ≫ (E).hom)
      (A (.inl 0)) (A (.inl 2)) := by
  apply (initialGlobalTensor_infinity_isPullback hπ data S j hj).of_iso'
    L (Iso.refl _) ci (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · rw [tensorShearInitialInfinitySlopeIso_inclusion]
    have H := coefficientShearInitialEquationIso_tensor_normal
      data S r j hj hs h3 h4 hr
    have H' := congrArg (· ≫ (ci).hom) H
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at H'
    simpa only [Category.assoc] using congrArg (p ≫ fiberIncidenceImmersion a c ≫ ·) H'
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- Both full actual atlas inclusions commute on the original shifted slope boundary. -/
@[reassoc] theorem coefficientShearInitialInfinitySlope_comp :
    b ≫ A (.inl 0) = p ≫ fiberIncidenceImmersion a c ≫ (E).hom ≫ A (.inl 2) := by
  simpa only [Category.assoc] using
    (coefficientShearInitialInfinity_isPullback hπ data S r j hj hs h3 h4 hr).w

end FLT.Mazur.WeierstrassDividedDepth
