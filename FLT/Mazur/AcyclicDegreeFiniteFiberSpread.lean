/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFiberOriginalOpenSpread
public import FLT.Mazur.UnpointedAcyclicDegreeOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Fixed-degree divisors on a whole finite inverse-image neighborhood

Actual geometric branch classes in the original acyclic degree locus
construct that condition on the entire inverse image of one affine base
open. The whole geometric base map factors through this open. The hypothesis
covers the base-changed distinguished fiber, not just original branch points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  {E U T : Over (Spec (.of R))} (p : E ⟶ U) [IsFinite p.left]
  {ι : Type*} (s : ι → (U ⟶ E)) (q : E ⟶ T)
  (c : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ)
  {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)} (z : Over.mk t ⟶ U)
local notation "η" => (default : Spec (CommRingCat.of K))

/-- Geometric branch divisors spread to the whole original finite inverse-image neighborhood. -/
theorem exists_affine_finite_fiber_acyclic_degree
    (hc : ∀ x : E.left, p.left x = z.left η → ∃ i, (s i).left (z.left η) = x)
    (hs : ∀ i, (relativeFppfSheaf f).obj.map (z ≫ s i ≫ q).op c ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t))) :
    ∃ W : U.left.Opens, IsAffineOpen W ∧
      (∃ w : Spec (.of K) ⟶ W.toScheme, w ≫ W.ι = z.left) ∧
      let E' : Over (Spec (.of R)) := Over.mk ((p.left ⁻¹ᵁ W).ι ≫ E.hom)
      let a : E' ⟶ E := Over.homMk (p.left ⁻¹ᵁ W).ι
      (relativeFppfSheaf f).obj.map (a ≫ q).op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op E') := by
  let D := unpointedAcyclicDegreeTest f T c d
  let j : D ⟶ T := unpointedAcyclicDegreeArrow f T c d
  have hp (i : ι) : q.left ((s i).left (z.left η)) ∈ Set.range j.left := by
    obtain ⟨a, ha, _⟩ :=
      (unpointedAcyclicDegreeOpen_represents f T c d (z ≫ s i ≫ q)).mp (hs i)
    exact ⟨a.left η, congrArg (fun g : Over.mk t ⟶ T ↦ g.left η) ha⟩
  obtain ⟨W, hW, hzW, b, hb⟩ := FiniteFiberOriginalOpenSpread.exists_affine_lift_of_sections
    p.left q.left j.left (fun i ↦ (s i).left) (z.left η) hc hp
  have hr : Set.range z.left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change z.left x ∈ W
    rwa [Subsingleton.elim (α := Spec (.of K)) x η]
  refine ⟨W, hW, ⟨IsOpenImmersion.lift W.ι z.left hr,
    IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩
  let E' : Over (Spec (.of R)) := Over.mk ((p.left ⁻¹ᵁ W).ι ≫ E.hom)
  let a : E' ⟶ E := Over.homMk (p.left ⁻¹ᵁ W).ι
  have hw : b ≫ D.hom = E'.hom := by
    rw [← j.w, ← Category.assoc, hb, Category.assoc, q.w]
    rfl
  let b' : E' ⟶ D := Over.homMk b hw
  apply (unpointedAcyclicDegreeOpen_represents f T c d (a ≫ q)).mpr
  refine ⟨b', Over.OverMorphism.ext hb, ?_⟩
  intro v hv
  exact (cancel_mono j).mp (hv.trans (Over.OverMorphism.ext hb).symm)

/-- All original geometric lifts construct a neighborhood without a supplied section family. -/
theorem exists_affine_etale_fiber_acyclic_degree [Etale p.left] [IsSepClosed K]
    (hs : ∀ a : Over.mk t ⟶ E, a ≫ p = z →
      (relativeFppfSheaf f).obj.map (a ≫ q).op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t))) :
    ∃ W : U.left.Opens, IsAffineOpen W ∧
      (∃ w : Spec (.of K) ⟶ W.toScheme, w ≫ W.ι = z.left) ∧
      let E' : Over (Spec (.of R)) := Over.mk ((p.left ⁻¹ᵁ W).ι ≫ E.hom)
      let a : E' ⟶ E := Over.homMk (p.left ⁻¹ᵁ W).ι
      (relativeFppfSheaf f).obj.map (a ≫ q).op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op E') := by
  let D := unpointedAcyclicDegreeTest f T c d
  let j : D ⟶ T := unpointedAcyclicDegreeArrow f T c d
  have hp (x : E.left) (hx : p.left x = z.left η) : q.left x ∈ Set.range j.left := by
    obtain ⟨a, ha, hax⟩ :=
      Scheme.exists_fac_of_etale_of_isSepClosed p.left z.left x hx
    let a' : Over.mk t ⟶ E := Over.homMk a (by
      rw [← p.w, ← Category.assoc, ha, z.w])
    obtain ⟨v, hv, _⟩ := (unpointedAcyclicDegreeOpen_represents f T c d (a' ≫ q)).mp
      (hs a' (Over.OverMorphism.ext ha))
    refine ⟨v.left η, ?_⟩
    exact (congrArg (fun g : Over.mk t ⟶ T ↦ g.left η) hv).trans
      (congrArg q.left hax)
  obtain ⟨W, hW, hzW, b, hb⟩ :=
    FiniteFiberOriginalOpenSpread.exists_affine_lift p.left q.left j.left (z.left η) hp
  have hr : Set.range z.left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change z.left x ∈ W
    rwa [Subsingleton.elim (α := Spec (.of K)) x η]
  refine ⟨W, hW, ⟨IsOpenImmersion.lift W.ι z.left hr,
    IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩
  let E' : Over (Spec (.of R)) := Over.mk ((p.left ⁻¹ᵁ W).ι ≫ E.hom)
  let a : E' ⟶ E := Over.homMk (p.left ⁻¹ᵁ W).ι
  have hw : b ≫ D.hom = E'.hom := by
    rw [← j.w, ← Category.assoc, hb, Category.assoc, q.w]
    rfl
  let b' : E' ⟶ D := Over.homMk b hw
  apply (unpointedAcyclicDegreeOpen_represents f T c d (a ≫ q)).mpr
  refine ⟨b', Over.OverMorphism.ext hb, ?_⟩
  intro v hv
  exact (cancel_mono j).mp (hv.trans (Over.OverMorphism.ext hb).symm)

end FLT.Mazur.CartierAbel
