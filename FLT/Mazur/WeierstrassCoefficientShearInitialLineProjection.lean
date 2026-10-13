/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearLineProjection
public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassCoefficientShearInitialSmooth
public import FLT.Mazur.WeierstrassDividedInitialGlobalStep

/-!
# Every original function on the complete initial coefficient line

Reconstruction and projection of the full initial line retain incidence and
root-shifted slope for arbitrary coefficient algebras and tangent roots.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
  (hs : algebraMap R S (π ^ start) = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "C" => coefficientShearInitialLine hπ data S r j hj hs h3 h4 hr
local notation "G" => coefficientShearGluedIso hπ data S r j hj
local notation "F" => tensorShearInitialLineMap W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 hr
local notation "f" => originalShearInitialLineMap W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 hr

/-- Reconstruction of the full initial line preserves every original tensor function. -/
@[reassoc] theorem coefficientShearInitialLine_tensor_reconstruction :
    C ≫ (G).hom = Spec.map (CommRingCat.ofHom (F).toRingHom) ≫
      globalInitialTensorChart hπ data S j hj := by
  rw [coefficientShearInitialLine, Category.assoc,
    coefficientShearInitialFiber_reconstruction, globalInitialCoefficientShearChart]
  simp only [← Category.assoc]
  apply congrArg (· ≫ globalInitialTensorChart hπ data S j hj)
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- Projection retains every original integral function on the entire initial line. -/
@[reassoc] theorem coefficientShearInitialLine_projection :
    C ≫ coefficientShearGluedProjection hπ data S r j hj =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ globalInitialChart hπ data j hj := by
  rw [coefficientShearGluedProjection,
    coefficientShearInitialLine_tensor_reconstruction_assoc,
    globalInitialTensorChart_integralProjection, ← Category.assoc]
  apply congrArg (· ≫ globalInitialChart hπ data j hj)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
