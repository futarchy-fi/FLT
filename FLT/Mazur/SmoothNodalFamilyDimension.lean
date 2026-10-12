/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodalGeometricFiberGenus
public import FLT.Mazur.SmoothConnectedFieldCurveDimension
public import FLT.Mazur.SmoothBaseChangeDimensionOpen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Relative dimension supplied by the original nodal fibers

The nodal fiber core gives connectedness and pure dimension one. For smooth
families these imply relative dimension one, first on geometric fibers and
then on actual neighborhoods of every point of the original family.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FCurve.CurveFiberHypotheses
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A smooth nodal field fiber has relative dimension one. -/
theorem NodalFiberCore.smooth_relativeDimension {K : Type} [Field K] {X : Scheme}
    {f : X ⟶ Spec (.of K)} (h : NodalFiberCore f) [Smooth f] :
    SmoothOfRelativeDimension 1 f := by
  let _ := h.connected
  exact smooth_connected_fieldCurve_relativeDimension f h.pureDimension.topologicalKrullDim_eq_one

/-- The original geometric fiber condition survives any cartesian square. -/
theorem NodalGeometricFibers.of_isPullback {X S Y T : Scheme}
    {f : X ⟶ S} (h : NodalGeometricFibers f) {g : Y ⟶ T} {i : Y ⟶ X} {b : T ⟶ S}
    (H : IsPullback i g f b) : NodalGeometricFibers g := by
  refine ⟨fun K _ _ s Z p q H' ↦ ?_⟩
  exact h.fiber K (s ≫ b) (p ≫ i) q (H'.paste_horiz H)

/-- Geometric nodal fibers determine the dimension of a smooth family over an affine base. -/
theorem NodalGeometricFibers.smooth_relativeDimension_spec
    {R : Type} [CommRing R] {X : Scheme} {f : X ⟶ Spec (.of R)}
    (h : NodalGeometricFibers f) [Smooth f] : SmoothOfRelativeDimension 1 f := by
  have hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ f) := by
    intro x
    let K := AlgebraicClosure (X.residueField x)
    let p : Spec (.of K) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x
    let g := p ≫ f
    let a := (Spec.preimage g).hom
    let _ := a.toAlgebra
    have hg : Spec.map (CommRingCat.ofHom (algebraMap R K)) = g := Spec.map_preimage g
    let q := pullback.snd f g
    let i := pullback.fst f g
    let l : Spec (.of K) ⟶ Limits.pullback f g := pullback.lift p (𝟙 _) (Category.id_comp _).symm
    let _ : SmoothOfRelativeDimension 1 q := (h.pullback g).smooth_relativeDimension
    have H : IsPullback i q f (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
      rw [hg]
      exact .of_hasPullback f g
    obtain ⟨V, hx, hd⟩ := SmoothBaseChangeDimensionOpen.exists_open f q i H 1
      (l (IsLocalRing.closedPoint K))
    have hi : i (l (IsLocalRing.closedPoint K)) = x := by
      change (l ≫ i) _ = x
      rw [pullback.lift_fst]
      exact X.fromSpecResidueField_apply x _
    exact ⟨V, hi ▸ hx, hd⟩
  choose V hx hd using hlocal
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) V
    (top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩) hd

/-- Smooth families with the original nodal fiber data have relative dimension one. -/
theorem NodalGeometricFibers.smooth_relativeDimension {X S : Scheme.{0}} {f : X ⟶ S}
    (h : NodalGeometricFibers f) [Smooth f] : SmoothOfRelativeDimension 1 f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension 1) S.affineCover
  intro i
  exact (h.baseChange (S.affineCover.f i)).smooth_relativeDimension_spec

end FLT.Mazur.FCurve.CurveFiberHypotheses
