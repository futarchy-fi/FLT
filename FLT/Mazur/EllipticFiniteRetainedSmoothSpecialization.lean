/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedSpecialization
public import FLT.Mazur.EllipticFiniteMiddleSpecialization
public import FLT.Mazur.WeierstrassDilatationHorizontalSmooth

/-!
# Smooth specialization on all retained primitive-depth components

An original primitive point strictly below middle depth has an integral
horizontal section. The entire residue horizontal open is smooth and is
retained by every later modification, so the original proper specialization
remains smooth in all those models.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
  (hp : 2 * (start + j) < depth)
local notation "k" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A k))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1 + r) hr)
local notation "c" => finiteRetainedBoundaryTensorChart A hπ data j hj r hr k

include D hj hk0 hk hp in
/-- The entire actual retained residue horizontal chart is smooth over the residue field. -/
theorem finiteRetainedBoundaryTensorChart_smooth : Smooth (c ≫ p) := by
  rw [finiteRetainedBoundaryTensorChart_structure]
  exact WeierstrassDilatation.residueHorizontalStructure_smooth D (start + j) hk0 hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

include D hj hk0 hk hp in
/-- Shallower original primitive points specialize smoothly in every later finite model. -/
theorem finitePointSpecialization_retained_smooth
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (v : NodePointCoordinates A W π P) (hv : v.depth = start + j) (x : Spec (.of k)) :
    let _ := finitePointSpecializationStructure_lfp A hπ data (j + 1 + r) hr
    finitePointSpecialization A hπ data (j + 1 + r) hr P x ∈ (p).smoothLocus := by
  let _ := finitePointSpecializationStructure_lfp A hπ data (j + 1 + r) hr
  obtain ⟨y, hy⟩ := finiteCoefficientPointSection_mem_retainedChart A hπ data j hj r hr k
    D hk0 hp P v hv x
  change c y = finitePointSpecialization A hπ data (j + 1 + r) hr P x at hy
  rw [← hy]
  apply (PolygonAtlas.mem_smooth_iff c p y).mpr
  let _ := finiteRetainedBoundaryTensorChart_smooth A hπ data D j hj r hr hk0 hk hp
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

end FLT.Mazur.WeierstrassDividedDepth
