/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassSuccessiveXMiddleFiberHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Arbitrary-target uniqueness on every original retained coefficient chart

The complete retained conic and both original lines detect the entire atlas chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "e" => coefficientShearMiddleEquiv W (π ^ (start + i.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4
local notation "E" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso (AlgEquiv.toRingEquiv e)))
local notation "G" => coefficientShearGluedIso hπ data S r t ht
local notation "s" => coefficientShearGluedStructure hπ data S r t ht
local notation "h2" => coefficientShear_a₂_zero W S r hr

local notation "C₀" => coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr
local notation "L" => coefficientShearRetainedLine hπ data S r t ht i hs hp h3 h4 hr
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  {Y : Scheme.{u}} (f g : coefficientShearGlued hπ data S r t ht ⟶ Y)


variable
  (hC : coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr ≫ f =
    coefficientShearRetainedConic hπ data S r t ht i hs hp h3 h4 hr ≫ g)

include ha hC
/-- The three full original components detect morphisms on the entire middle equation. -/
theorem coefficientShearRetainedFiber_hom_ext
    (h₁ : L 0 (middle_first_root U) ≫ f = L 0 (middle_first_root U) ≫ g)
    (h₂ : L (-a) (middle_second_root U) ≫ f = L (-a) (middle_second_root U) ≫ g) :
    coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4 ≫ f =
      coefficientShearRetainedFiber hπ data S r t ht i hs hp h3 h4 ≫ g := by
  apply middleFiber_components_hom_ext U c h2 ha
  · simpa only [coefficientShearRetainedConic, Category.assoc] using hC
  · simpa only [coefficientShearRetainedLine, Category.assoc] using h₁
  · simpa only [coefficientShearRetainedLine, Category.assoc] using h₂

/-- The same complete components detect the original retained atlas chart. -/
theorem coefficientShearRetainedChart_hom_ext
    (h₁ : L 0 (middle_first_root U) ≫ f = L 0 (middle_first_root U) ≫ g)
    (h₂ : L (-a) (middle_second_root U) ≫ f = L (-a) (middle_second_root U) ≫ g) :
    coefficientShearGluedChart hπ data S r t ht (.inr i) ≫ f =
      coefficientShearGluedChart hπ data S r t ht (.inr i) ≫ g := by
  have h := coefficientShearRetainedFiber_hom_ext
    hπ data S r t ht i hs hp h3 h4 hr ha f g hC h₁ h₂
  unfold coefficientShearRetainedFiber at h
  rw [Category.assoc, Category.assoc] at h
  exact (cancel_epi _).mp h

end FLT.Mazur.WeierstrassDividedDepth
