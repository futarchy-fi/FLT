/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricFiniteGroundInterior
public import FLT.Mazur.GeometricFullInteriorFiniteKernel

/-!
# Constructed finite-model kernels through arbitrary original geometric classes

The original class constructs translations, affine retention, a full fiber,
a finite-free ground refinement, and a norm neighborhood. The resulting
finite-model kernel is for the changed family. Its source still maps to the
original chart with the exact original geometric morphism and Picard class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))
local instance {S : Type} [CommRing S] (a : Spec (.of S) ⟶ Spec (.of R)) :
    SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance

include hL in
/-- A constructed changed-family finite kernel retains the arbitrary original geometric class. -/
theorem exists_arbitrary_geometric_finite_kernel
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeLocus f hL d V c k ∧
      ∃ (S : Type) (_ : CommRing S) (_ : Algebra.FiniteType ℤ S)
        (a : Spec (.of S) ⟶ Spec (.of R)) (W : Over (Spec (.of S)))
        (_ : IsAffine W.left) (_ : Etale W.hom) (_ : IsFinite W.hom)
        (_ : Surjective W.hom) (v : (Over.map a).obj W ⟶ V),
        Etale a ∧ Etale v.left ∧
        ∃ (C : Over (Spec (.of S))) (_ : IsAffine C.left)
          (u : C ⟶ groundBaseSource f a hL d V W v k) (_ : IsOpenImmersion u.left)
          (l : C ⟶ variableHilbertTest (pullback.snd f a) d W)
          (_ : IsOpenImmersion l.left) (z : Spec (.of K) ⟶ C.left),
          l = u ≫ groundBaseSourceChart f a hL d V W v k ∧
          z ≫ u.left ≫ (groundBaseSourceMap f a hL d V W v k).left = b.left ∧
          z ≫ C.hom ≫ a = t ∧
          IsPullback
            (fst (pullback.snd f a) (fixedBaseAmple f a hL) d W
              (fixedBaseTranslationClass f a V W v c) l).left
            (snd (pullback.snd f a) (fixedBaseAmple f a hL) d W
              (fixedBaseTranslationClass f a V W v c) l).left
            (finiteKernelProjection (pullback.snd f a) (fixedBaseAmple f a hL) d W
              (fixedBaseTranslationClass f a V W v c) l).left
            (finiteKernelProjection (pullback.snd f a) (fixedBaseAmple f a hL) d W
              (fixedBaseTranslationClass f a V W v c) l).left := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    S, hS, hZ, a, W, hW, hWe, hWf, hWs, v, ha, hv, hB, z, hz, hzt, hi⟩ :=
    exists_arbitrary_geometric_finite_ground_interior f hL t s
  let _ := hV
  let _ := he
  let _ := hA
  let _ := hk
  let B := groundBaseSource f a hL d V W v k
  let t' : Spec (.of K) ⟶ Spec (.of S) := z ≫ B.hom
  let z' : Over.mk t' ⟶ B := Over.homMk z
  obtain ⟨n, ⟨e⟩⟩ := hB
  obtain ⟨C, hC, u, hu, l, hl, w, hw, hlu, _, hker⟩ :=
    exists_geometric_fullInterior_finite_kernel (pullback.snd f a) (fixedBaseAmple f a hL)
      d W (fixedBaseTranslationClass f a V W v c)
      (groundBaseSourceChart f a hL d V W v k) e z' hi
  have hwz : w.left ≫ u.left = z := congrArg Over.Hom.left hw
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    S, hS, hZ, a, W, hW, hWe, hWf, hWs, v, ha, hv,
    C, hC, u, hu, l, hl, w.left, hlu, ?_, ?_, hker⟩
  · rw [← Category.assoc, hwz, hz]
  · rw [← Category.assoc, w.w]
    exact hzt

end FLT.Mazur.HilbertChart.AffineRestriction
