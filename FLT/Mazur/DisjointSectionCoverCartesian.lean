/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionCartesianKernel
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Disjoint section covers in actual cartesian squares

Compatible base-changed sections remain open, disjoint and cover every
point of the full pullback. The coverage argument uses the cartesian
section square, so conjugate residue branches cannot be discarded.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.DisjointSectionCoverCartesian
universe u
variable {E U E' U' : Scheme.{u}} {p : E ⟶ U} {q : U' ⟶ U}
  {h : E' ⟶ E} {p' : E' ⟶ U'} (H : IsPullback h p' p q)
  {ι : Type*} (s : ι → (U ⟶ E)) (r : ι → (U' ⟶ E'))
  (hs : ∀ i, s i ≫ p = 𝟙 U) (hr : ∀ i, r i ≫ p' = 𝟙 U')
  (he : ∀ i, r i ≫ h = q ≫ s i)

include H hs hr he in
/-- Each actual extended section is open whenever the original section is open. -/
theorem isOpenImmersion [∀ i, IsOpenImmersion (s i)] (i : ι) :
    IsOpenImmersion (r i) :=
  MorphismProperty.of_isPullback
    (FCurve.section_isPullback_of_cartesian H (r i) (s i) (hr i) (hs i) (he i)).flip
    (inferInstanceAs (IsOpenImmersion (s i)))

include H hs hr he in
/-- Complete original sections cover the entire cartesian source after every base change. -/
theorem covers (hc : ∀ x : E, ∃ i, s i (p x) = x) :
    ∀ x : E', ∃ i, r i (p' x) = x := by
  intro x
  obtain ⟨i, hi⟩ := hc (h x)
  have hx : h x = s i (q (p' x)) := by
    have heq := congrArg (fun a : E' ⟶ U ↦ a x) H.w
    exact hi.symm.trans (congrArg (s i) heq)
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (FCurve.section_isPullback_of_cartesian H (r i) (s i) (hr i) (hs i) (he i))
    x (q (p' x)) hx
  have hw' : w = p' x := by
    have heq := congrArg p' hw
    change (r i ≫ p') w = p' x at heq
    rw [hr] at heq
    exact heq
  exact ⟨i, hw' ▸ hw⟩

include he in
/-- Independent original sheets remain disjoint in the full cartesian source. -/
theorem disjoint
    (hd : Pairwise (fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j)))) :
    Pairwise (fun i j ↦ Disjoint (Set.range (r i)) (Set.range (r j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨v, hv⟩ ⟨w, hw⟩
  have heq := congrArg h (hv.trans hw.symm)
  change (r i ≫ h) v = (r j ≫ h) w at heq
  rw [he, he] at heq
  exact Set.disjoint_left.mp (hd hij) ⟨q v, rfl⟩ ⟨q w, heq.symm⟩

end FLT.Mazur.DisjointSectionCoverCartesian
