/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassModificationXFullFiberHomExt

/-!
# Arbitrary-target uniqueness on the actual initial coefficient chart

Its complete incidence line and conic detect the whole original sheared equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
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
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6
local notation "L" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr
local notation "C₀" => coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)

variable {Y : Scheme.{u}}
  (f g : coefficientShearGlued hπ data S r j hj ⟶ Y)
  (hL : coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr ≫ f =
    coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr ≫ g)
  (hC : coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr ≫ f =
    coefficientShearInitialConic hπ data S r j hj hs h3 h4 hr ≫ g)

include ha hL hC
/-- The two complete pieces determine every map on the actual initial coefficient chart. -/
theorem coefficientShearInitialFiber_hom_ext :
    coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr ≫ f =
      coefficientShearInitialFiber hπ data S r j hj hs h3 h4 hr ≫ g := by
  apply fullFiber_components_hom_ext a c ha
  · simpa only [coefficientShearInitialLine, Category.assoc] using hL
  · simpa only [coefficientShearInitialConic, Category.assoc] using hC

/-- Agreement on the same pieces determines the entire initial atlas chart. -/
theorem coefficientShearInitialChart_hom_ext :
    coefficientShearGluedChart hπ data S r j hj (.inl 2) ≫ f =
      coefficientShearGluedChart hπ data S r j hj (.inl 2) ≫ g := by
  have h := coefficientShearInitialFiber_hom_ext hπ data S r j hj hs h3 h4 hr ha f g hL hC
  unfold coefficientShearInitialFiber at h
  rw [Category.assoc, Category.assoc] at h
  exact (cancel_epi _).mp h

end FLT.Mazur.WeierstrassDividedDepth
