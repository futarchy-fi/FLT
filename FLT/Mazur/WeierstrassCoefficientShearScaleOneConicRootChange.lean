/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootChange
public import FLT.Mazur.WeierstrassSuccessiveShearConicRootChange
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Signed conic punctures in both complete chosen-root models

The original tensor-function comparison and retained chart reconstruction
identify both actual conic embeddings in the entire model, with signs unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r s : S)
  (j k : ℕ) (hj : j ≤ n) (hk : k + 1 ≤ j)
  (hscale : algebraMap R S (π ^ (start + k)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨k + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨k + 1, by omega⟩).b4 = 0)
  (hc : algebraMap R S (data ⟨k + 1, by omega⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (hs : s ^ 2 + algebraMap R S W.a₁ * s - algebraMap R S W.a₂ = 0)
local notation "d" => data (Fin.mk (k + 1) (by omega))
local notation "c" => algebraMap R S (Data.b6 d)
local notation "Ur" => rootShearCurve (W.map (algebraMap R S)) r
local notation "Us" => rootShearCurve (W.map (algebraMap R S)) s
local notation "C" => coefficientShearRootChange hπ data S r s j hj
local notation "Fr" => tensorShearScaleOneConicImmersion W (π ^ (start + k)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hscale hp h3 h4 hr
local notation "Fs" => tensorShearScaleOneConicImmersion W (π ^ (start + k)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S s hscale hp h3 h4 hs
local notation "Br" => coefficientShearRetainedTensorChart hπ data S r j hj ⟨k, by omega⟩
local notation "Bs" => coefficientShearRetainedTensorChart hπ data S s j hj ⟨k, by omega⟩

include hk in
/-- The full first conic puncture becomes the signed opposite puncture in the other model. -/
theorem coefficientShearRootChange_scaleOneConicFirst
    (hrs : r + s = -algebraMap R S W.a₁) :
    (Spec.map (CommRingCat.ofHom (conicPuncturedFirst Ur c hc).toRingHom) ≫ Fr ≫ Br) ≫
        (C).hom =
      Spec.map (CommRingCat.ofHom (conicPuncturedSecond Us c hc).toRingHom) ≫ Fs ≫ Bs := by
  simp only [Category.assoc,
    coefficientShearRootChange_retainedTensorChart hπ data S r s j hj k hk]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun f => f ≫ Bs)
    (tensorShearScaleOneConicFirst_spec_rootChange W (π ^ (start + k)) π
      (d).b3 (d).b4 (d).b6 S r s hscale hp h3 h4 hr hs hc hrs)

include hk in
/-- The complete opposite conic puncture becomes the first, with its actual signed parameter. -/
theorem coefficientShearRootChange_scaleOneConicSecond
    (hrs : r + s = -algebraMap R S W.a₁) :
    (Spec.map (CommRingCat.ofHom (conicPuncturedSecond Ur c hc).toRingHom) ≫ Fr ≫ Br) ≫
        (C).hom =
      Spec.map (CommRingCat.ofHom (conicPuncturedFirst Us c hc).toRingHom) ≫ Fs ≫ Bs := by
  simp only [Category.assoc,
    coefficientShearRootChange_retainedTensorChart hπ data S r s j hj k hk]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun f => f ≫ Bs)
    (tensorShearScaleOneConicSecond_spec_rootChange W (π ^ (start + k)) π
      (d).b3 (d).b4 (d).b6 S r s hscale hp h3 h4 hr hs hc hrs)

end FLT.Mazur.WeierstrassDividedDepth
