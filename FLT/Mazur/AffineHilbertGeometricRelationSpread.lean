/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertAcyclicBranchLift
public import FLT.Mazur.SchemeFiniteGeometricOpenSpread

/-!
# Spreading acyclic retained branches to actual original relation maps

Once the independent envelope maps exist on a common test, their geometric
acyclicity and original chart retention extend to actual relation maps on
one affine open. Every envelope coordinate is preserved exactly. The proof
constructs the geometric arrows from divisor classes before spreading them.
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
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
  {T : Over (Spec (.of R))} (b : T ⟶ A)
  {ι : Type} [Finite ι] (e : ι → (T ⟶ prod A V)) (he : ∀ i, e i ≫ prod.fst = b)
  {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)} (z : Over.mk t ⟶ T)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "σ" => sectionAt f hL d V c k
local notation "s" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op (z ≫ b)) σ
local notation "j" => toEnvelope f hL d V c k

include he in
/-- Geometric acyclic classes retained by the original chart spread simultaneously. -/
theorem exists_acyclic_relation_spread
    (hA : ∀ i, s * (relativeFppfSheaf f).obj.map (z ≫ e i ≫ prod.snd).op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)))
    (hr : ∀ i, (acyclicTranslationLift f hL d V c s (z ≫ e i ≫ prod.snd) (hA i)).left
      η ∈ Set.range k.left) :
    ∃ (W : Over (Spec (.of R))) (q : W ⟶ T) (w : Over.mk t ⟶ W)
      (a : ι → (W ⟶ relation f hL d V c k)),
      IsAffine W.left ∧ IsOpenImmersion q.left ∧ w ≫ q = z ∧
      (∀ i, a i ≫ j = q ≫ e i) := by
  have hl (i : ι) := exists_acyclic_geometric_relation_lift f hL d V c k (z ≫ b)
    (z ≫ e i ≫ prod.snd) rfl (hA i) η (hr i)
  choose g hg using hl
  have hg' (i : ι) : g i ≫ j = z ≫ e i := by
    rw [hg]
    apply prod.hom_ext
    · rw [prod.lift_fst, Category.assoc, he]
    · rw [prod.lift_snd, Category.assoc]
  have hp (i : ι) : (e i).left (z.left η) ∈ Set.range (j).left :=
    ⟨(g i).left η, congrArg (fun a : Over.mk t ⟶ prod A V ↦ a.left η) (hg' i)⟩
  obtain ⟨W, q, w, a, hW, hq, hw, ha⟩ :=
    SchemeFiniteGeometricOpenSpread.exists_lifts (fun _ ↦ (prod A V).left)
      (fun _ ↦ (relation f hL d V c k).left) (fun _ ↦ (j).left)
      (fun i ↦ (e i).left) z.left hp
  let U : Over (Spec (.of R)) := Over.mk (q ≫ T.hom)
  let q' : U ⟶ T := Over.homMk q
  let w' : Over.mk t ⟶ U := Over.homMk w (by
    change w ≫ q ≫ T.hom = t
    rw [← Category.assoc, hw, z.w]
    rfl)
  have hw' (i : ι) : a i ≫ (relation f hL d V c k).hom = U.hom := by
    rw [← (j).w, ← Category.assoc, ha, Category.assoc, (e i).w]
    rfl
  let a' (i : ι) : U ⟶ relation f hL d V c k := Over.homMk (a i) (hw' i)
  exact ⟨U, q', w', a', hW, hq, Over.OverMorphism.ext hw,
    fun i ↦ Over.OverMorphism.ext (ha i)⟩

end FLT.Mazur.HilbertChart.AffineRestriction
