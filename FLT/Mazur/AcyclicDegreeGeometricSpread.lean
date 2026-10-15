/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicDegreeOpen
public import FLT.Mazur.SchemeFiniteGeometricOpenSpread

/-!
# Simultaneous fixed-degree acyclicity around a geometric test

For finitely many actual original Picard sections, acyclic divisor classes
of the specified degrees on a field test extend to a common affine open of
the original test scheme. The resulting membership supplies actual full
divisors there; no neighborhood or divisor family is assumed in advance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  {T : Over (Spec (.of R))} {ι : Type} [Finite ι]
  (s : ι → (relativeFppfSheaf f).obj.obj (op T)) (d : ι → ℕ)
  {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ T)
local notation "η" => (default : Spec (CommRingCat.of K))

/-- Actual finite degree conditions on a geometric test extend to one original affine open. -/
theorem exists_affine_acyclic_degree_spread
    (hs : ∀ i, (relativeFppfSheaf f).obj.map b.op (s i) ∈
      (acyclicDegreePicardSubfunctor f (d i)).obj (op (Over.mk t))) :
    ∃ (U : Over (Spec (.of R))) (q : U ⟶ T) (z : Over.mk t ⟶ U),
      IsAffine U.left ∧ IsOpenImmersion q.left ∧ z ≫ q = b ∧
      ∀ i, (relativeFppfSheaf f).obj.map q.op (s i) ∈
        (acyclicDegreePicardSubfunctor f (d i)).obj (op U) := by
  let D (i : ι) := unpointedAcyclicDegreeTest f T (s i) (d i)
  let j (i : ι) : D i ⟶ T := unpointedAcyclicDegreeArrow f T (s i) (d i)
  have hp (i : ι) : b.left η ∈ Set.range (j i).left := by
    obtain ⟨a, ha, _⟩ := (unpointedAcyclicDegreeOpen_represents f T (s i) (d i) b).mp (hs i)
    exact ⟨a.left η, congrArg (fun g : Over.mk t ⟶ T ↦ g.left η) ha⟩
  obtain ⟨U, q, z, a, hU, hq, hz, ha⟩ :=
    SchemeFiniteGeometricOpenSpread.exists_lifts (fun _ ↦ T.left) (fun i ↦ (D i).left)
      (fun i ↦ (j i).left) (fun _ ↦ 𝟙 T.left) b.left (by simpa using hp)
  let W : Over (Spec (.of R)) := Over.mk (q ≫ T.hom)
  let q' : W ⟶ T := Over.homMk q
  let z' : Over.mk t ⟶ W := Over.homMk z (by
    change z ≫ q ≫ T.hom = t
    rw [← Category.assoc, hz, b.w]
    rfl)
  have ha' (i : ι) : a i ≫ (j i).left = q := by simpa using ha i
  have hw (i : ι) : a i ≫ (D i).hom = W.hom := by
    rw [← (j i).w, ← Category.assoc, ha']
    rfl
  let a' (i : ι) : W ⟶ D i := Over.homMk (a i) (hw i)
  refine ⟨W, q', z', hU, hq, Over.OverMorphism.ext hz, fun i ↦ ?_⟩
  apply (unpointedAcyclicDegreeOpen_represents f T (s i) (d i) q').mpr
  refine ⟨a' i, Over.OverMorphism.ext (ha' i), ?_⟩
  intro v hv
  apply (cancel_mono (j i)).mp
  exact hv.trans (Over.OverMorphism.ext (ha' i)).symm

end FLT.Mazur.CartierAbel
