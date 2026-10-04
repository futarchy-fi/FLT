/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Finite-stage boundaries in sequential cochain systems

Lift a bounding cochain at a later stage, then kill its discrepancy at one
further stage. This is the cochain argument needed for localization of a
section-twist system; its hypotheses concern actual terms and transition maps.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace FLT.Mazur.SequentialCochainBoundary

variable (F G : ℕ ⥤ CochainComplex AddCommGrpCat.{u} ℕ) (a : F ⟶ G)

/-- A cochain map commutes with the differential on elements. -/
lemma map_d {K L : CochainComplex AddCommGrpCat.{u} ℕ} (b : K ⟶ L)
    (i j : ℕ) (x : K.X i) : L.d i j (b.f i x) = b.f j (K.d i j x) :=
  ConcreteCategory.congr_hom (b.comm i j) x

/-- Naturality at each cochain degree, on actual elements. -/
lemma naturality_apply {n m : ℕ} (h : n ≤ m) (q : ℕ) (x : (F.obj n).X q) :
    (a.app m).f q ((F.map (homOfLE h)).f q x) =
      (G.map (homOfLE h)).f q ((a.app n).f q x) :=
  ConcreteCategory.congr_hom
    (congrArg (fun b ↦ b.f q) (a.naturality (homOfLE h))) x

/-- Boundaries lift at a finite stage if cochains lift and restriction kernels die. -/
theorem exists_boundary_at_stage (q : ℕ)
    (hExact : ∀ n, (G.obj n).ExactAt (q + 1))
    (hLift : ∀ n (b : (G.obj n).X q), ∃ (m : ℕ) (h : n ≤ m) (c : (F.obj m).X q),
      (a.app m).f q c = (G.map (homOfLE h)).f q b)
    (hKill : ∀ n (x : (F.obj n).X (q + 1)), (a.app n).f (q + 1) x = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (F.map (homOfLE h)).f (q + 1) x = 0)
    (n : ℕ) (z : (F.obj n).X (q + 1))
    (hz : (F.obj n).d (q + 1) (q + 2) z = 0) :
    ∃ (m : ℕ) (h : n ≤ m) (b : (F.obj m).X q),
      (F.obj m).d q (q + 1) b = (F.map (homOfLE h)).f (q + 1) z := by
  have he := hExact n
  rw [(G.obj n).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff_function_exact] at he
  have hz' : (G.obj n).d (q + 1) (q + 2) ((a.app n).f (q + 1) z) = 0 := by
    rw [map_d, hz, map_zero]
  obtain ⟨b, hb⟩ := (he _).mp hz'
  change (G.obj n).X q at b
  change (G.obj n).d q (q + 1) b = (a.app n).f (q + 1) z at hb
  obtain ⟨m, hnm, c, hc⟩ := hLift n b
  let x : (F.obj m).X (q + 1) :=
    (F.map (homOfLE hnm)).f (q + 1) z - (F.obj m).d q (q + 1) c
  have hx : (a.app m).f (q + 1) x = 0 := by
    dsimp only [x]
    rw [map_sub, naturality_apply, ← map_d, hc, map_d, hb, sub_self]
  obtain ⟨l, hml, hl⟩ := hKill m x hx
  refine ⟨l, hnm.trans hml, (F.map (homOfLE hml)).f q c, ?_⟩
  have hdiff : (F.map (homOfLE hml)).f (q + 1)
      ((F.map (homOfLE hnm)).f (q + 1) z) =
      (F.map (homOfLE hml)).f (q + 1) ((F.obj m).d q (q + 1) c) := by
    exact sub_eq_zero.mp ((map_sub _ _ _).symm.trans hl)
  rw [map_d, ← hdiff]
  have hcomp : homOfLE (hnm.trans hml) = homOfLE hnm ≫ homOfLE hml := rfl
  rw [hcomp, F.map_comp]
  rfl

/-- A finite-stage boundary statement kills the actual categorical homology classes. -/
theorem homology_annihilator_of_boundaries (q : ℕ)
    (hBoundary : ∀ n (z : (F.obj n).X (q + 1)),
      (F.obj n).d (q + 1) (q + 2) z = 0 →
      ∃ (m : ℕ) (h : n ≤ m) (b : (F.obj m).X q),
        (F.obj m).d q (q + 1) b = (F.map (homOfLE h)).f (q + 1) z)
    (n : ℕ) (x : (F.obj n).homology (q + 1)) :
    ∃ (m : ℕ) (h : n ≤ m), HomologicalComplex.homologyMap (F.map (homOfLE h)) (q + 1) x = 0 := by
  obtain ⟨z, rfl⟩ :=
    ((AddCommGrpCat.epi_iff_surjective ((F.obj n).homologyπ (q + 1))).mp inferInstance) x
  have hz : (F.obj n).d (q + 1) (q + 2) ((F.obj n).iCycles (q + 1) z) = 0 :=
    ConcreteCategory.congr_hom ((F.obj n).iCycles_d (q + 1) (q + 2)) z
  obtain ⟨m, h, b, hb⟩ := hBoundary n _ hz
  refine ⟨m, h, ?_⟩
  let f := F.map (homOfLE h)
  have hc : HomologicalComplex.cyclesMap f (q + 1) z =
      (F.obj m).toCycles q (q + 1) b := by
    apply (AddCommGrpCat.mono_iff_injective ((F.obj m).iCycles (q + 1))).mp inferInstance
    change (HomologicalComplex.cyclesMap f (q + 1) ≫ (F.obj m).iCycles (q + 1)) z =
      ((F.obj m).toCycles q (q + 1) ≫ (F.obj m).iCycles (q + 1)) b
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.toCycles_i]
    exact hb.symm
  change ((F.obj n).homologyπ (q + 1) ≫ HomologicalComplex.homologyMap f (q + 1)) z = 0
  rw [HomologicalComplex.homologyπ_naturality]
  change (F.obj m).homologyπ (q + 1) (HomologicalComplex.cyclesMap f (q + 1) z) = 0
  rw [hc, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
  rfl

end FLT.Mazur.SequentialCochainBoundary
