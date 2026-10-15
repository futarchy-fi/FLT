/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGeometricEtaleSpread
public import FLT.Mazur.AffineHilbertGeometricRelationSpread
public import FLT.Mazur.AffineHilbertGeometricAcyclicFiber

/-!
# Constructed original relation families on affine étale neighborhoods

Combine the independent envelope spreading with simultaneous acyclic and
retention opens. The resulting finite family consists of actual ORIGINAL
relation maps on a finitely presented affine étale neighborhood. On the
geometric test their envelope coordinates enumerate the original fiber.
Geometric acyclicity and retention remain explicit inputs, not coverage claims.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  {K : Type} [Field K] [IsSepClosed K]
  {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "σ" => sectionAt f hL d V c k
local notation "s" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) σ
local notation "j" => toEnvelope f hL d V c k
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- All concrete geometric Hilbert conditions spread to one original affine étale neighborhood. -/
theorem exists_retained_etale_relation_neighborhood
    (hA : ∀ v : Over.mk t ⟶ V, s * (relativeFppfSheaf f).obj.map v.op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)))
    (hr : ∀ v : Over.mk t ⟶ V,
      (acyclicTranslationLift f hL d V c s v (hA v)).left η ∈ Set.range k.left) :
    ∃ (W : Over (Spec (.of R))) (q : W ⟶ A) (w : Over.mk t ⟶ W)
      (a : Fin (π ⁻¹' {b.left η}).ncard → (W ⟶ relation f hL d V c k)),
      IsAffine W.left ∧ Etale q.left ∧ q.left.appTop.hom.FinitePresentation ∧
      w ≫ q = b ∧ (∀ i, a i ≫ snd f hL d V c k = q) ∧
      Function.Injective (fun i ↦ (w ≫ a i ≫ j).left η) ∧
      Set.range (fun i ↦ (w ≫ a i ≫ j).left η) = π ⁻¹' {b.left η} := by
  obtain ⟨U, q, z, e, hU, hq, _, hz, he, hi, hE⟩ := exists_independent_etale_spread V b
  have hA' (i) : (relativeFppfSheaf f).obj.map (z ≫ q).op σ *
      (relativeFppfSheaf f).obj.map (z ≫ e i ≫ prod.snd).op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
    rw [hz]
    exact hA (z ≫ e i ≫ prod.snd)
  have hr' (i) : (acyclicTranslationLift f hL d V c
      ((relativeFppfSheaf f).obj.map (z ≫ q).op σ)
      (z ≫ e i ≫ prod.snd) (hA' i)).left η ∈ Set.range k.left := by
    simpa only [hz] using hr (z ≫ e i ≫ prod.snd)
  obtain ⟨W, u, w, a, hW, hu, hw, ha⟩ :=
    exists_acyclic_relation_spread f hL d V c k q e he z hA' hr'
  have hae (i) : w ≫ a i ≫ j = z ≫ e i := by
    rw [ha, ← Category.assoc, hw]
  have hap (i) : a i ≫ snd f hL d V c k = u ≫ q := by
    rw [← toEnvelope_test, ← Category.assoc, ha, Category.assoc, he]
  refine ⟨W, u ≫ q, w, a, hW,
    inferInstanceAs (Etale (u.left ≫ q.left)),
    (u.left ≫ q.left).finitePresentation_appTop, ?_, hap, ?_, ?_⟩
  · rw [← Category.assoc, hw, hz]
  · simpa only [hae] using hi
  · simpa only [hae] using hE

end FLT.Mazur.HilbertChart.AffineRestriction
