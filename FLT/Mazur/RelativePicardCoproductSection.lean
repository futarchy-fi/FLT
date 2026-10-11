/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfComparisonCover

/-!
# Assembling original Picard sections on a small disjoint union

Independent sections on original relative tests glue to one section on their
actual scheme coproduct. The disjointness proof uses the empty-test sheaf
condition, so no compatibility between different components is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original Picard sheaf has only one section on an empty test. -/
theorem relativeFppf_eq_of_isEmpty (T : Over S) [IsEmpty T.left]
    (a b : (relativeFppfSheaf f).obj.obj (op T)) : a = b := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  have hc : Sieve.ofArrows (fun i : Empty ↦ i.elim : Empty → Over S)
      (fun i ↦ i.elim : ∀ i : Empty, Empty.elim i ⟶ T) ∈
      (Scheme.fppfTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.generate_mem_toGrothendieck
      (Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation)
        (X := T.left) Empty (fun i ↦ (i.elim : Over S).left)
        (fun i ↦ (show (i.elim : Over S) ⟶ T from i.elim).left)
        (fun x ↦ isEmptyElim x)
        (fun i ↦ i.elim)).mem₀
  apply (hs.isSeparated _ hc).ext
  rintro U g ⟨V, h, k, ⟨i⟩, _⟩
  exact i.elim

variable {ι : Type u} (T : ι → Over S)

/-- The actual disjoint union of the original relative tests. -/
def relativeCoproductTest : Over S :=
  Over.mk (Sigma.desc (fun i ↦ (T i).hom))

/-- Each unchanged test maps into the actual disjoint union. -/
def relativeCoproductArrow (i : ι) : T i ⟶ relativeCoproductTest T :=
  Over.homMk (Sigma.ι (fun j ↦ (T j).left) i) (Sigma.ι_comp_desc _ _)

/-- The component arrows form an actual covering sieve of the relative coproduct. -/
theorem relativeCoproduct_covering :
    Sieve.ofArrows T (relativeCoproductArrow T) ∈
      (Scheme.fppfTopology.over S) (relativeCoproductTest T) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _
      (AlgebraicGeometry.sigmaOpenCover (fun i ↦ (T i).left)).mem₀)

/-- Arbitrarily chosen component sections are compatible on all coproduct overlaps. -/
theorem relativeCoproduct_compatible
    (s : ∀ i, (relativeFppfSheaf f).obj.obj (op (T i))) :
    Presieve.Arrows.Compatible ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (relativeCoproductArrow T) s := by
  intro i j U a b hab
  by_cases hij : i = j
  · subst j
    have he : a = b := by
      apply Over.OverMorphism.ext
      exact (cancel_mono (Sigma.ι (fun j ↦ (T j).left) i)).mp
        (congrArg (fun z ↦ z.left) hab)
    subst b
    rfl
  · let _ : IsEmpty U.left := AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
      (g := fun j ↦ (T j).left)
      (show CommSq a.left b.left (Sigma.ι (fun j ↦ (T j).left) i)
        (Sigma.ι (fun j ↦ (T j).left) j) from ⟨congrArg (fun z ↦ z.left) hab⟩) hij
    exact relativeFppf_eq_of_isEmpty f U _ _

/-- Independent sections assemble uniquely on the actual original relative coproduct. -/
theorem relativeCoproduct_section_existsUnique
    (s : ∀ i, (relativeFppfSheaf f).obj.obj (op (T i))) :
    ∃! t : (relativeFppfSheaf f).obj.obj (op (relativeCoproductTest T)),
      ∀ i, (relativeFppfSheaf f).obj.map (relativeCoproductArrow T i).op t = s i := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  have h := hs.isSheafFor _ (relativeCoproduct_covering T)
  rw [Presieve.isSheafFor_arrows_iff] at h
  exact h s (relativeCoproduct_compatible f T s)

/-- The assembled section, with no relation required among the input sections. -/
def relativeCoproductSection (s : ∀ i, (relativeFppfSheaf f).obj.obj (op (T i))) :
    (relativeFppfSheaf f).obj.obj (op (relativeCoproductTest T)) :=
  (relativeCoproduct_section_existsUnique f T s).choose

/-- Restriction recovers the original component section. -/
theorem relativeCoproductSection_map
    (s : ∀ i, (relativeFppfSheaf f).obj.obj (op (T i))) (i : ι) :
    (relativeFppfSheaf f).obj.map (relativeCoproductArrow T i).op
      (relativeCoproductSection f T s) = s i :=
  (relativeCoproduct_section_existsUnique f T s).choose_spec.1 i

/-- Sections on the disjoint union are determined by their original component restrictions. -/
theorem relativeCoproductSection_ext
    {a b : (relativeFppfSheaf f).obj.obj (op (relativeCoproductTest T))}
    (h : ∀ i, (relativeFppfSheaf f).obj.map (relativeCoproductArrow T i).op a =
      (relativeFppfSheaf f).obj.map (relativeCoproductArrow T i).op b) : a = b := by
  let s i := (relativeFppfSheaf f).obj.map (relativeCoproductArrow T i).op b
  obtain ⟨t, _, ht⟩ := relativeCoproduct_section_existsUnique f T s
  exact (ht a h).trans (ht b (fun _ ↦ rfl)).symm

end FLT.Mazur.SchemePicard
