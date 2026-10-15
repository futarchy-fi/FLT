/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardCoproductSection

/-!
# Independent Picard classes on an actual disjoint section cover

The original fppf sheaf glues arbitrary classes on disjoint open sections
uniquely to the whole original source. Empty overlaps give compatibility;
no compatibility equations or descended section are supplied as hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemePicard
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) {E U : Over S}
  (p : E ⟶ U) {ι : Type u} (a : ι → (U ⟶ E)) [∀ i, IsOpenImmersion (a i).left]
  (hc : ∀ x : E.left, ∃ i, (a i).left (p.left x) = x)
  (hd : Pairwise (fun i j ↦ Disjoint (Set.range (a i).left) (Set.range (a j).left)))

include hc in
/-- The original open sections give a covering sieve of the unchanged original test. -/
theorem disjointSection_covering :
    Sieve.ofArrows (fun _ : ι ↦ U) a ∈ (Scheme.fppfTopology.over S) E := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _
      (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (X := E.left) ι
        (fun _ ↦ U.left) (fun i ↦ (a i).left)
        (fun x ↦ by obtain ⟨i, hi⟩ := hc x; exact ⟨i, p.left x, hi⟩)
        (fun _ ↦ inferInstance)).mem₀)

include hd in
/-- Disjointness proves compatibility for arbitrary original component Picard classes. -/
theorem disjointSection_compatible
    (c : ι → (relativeFppfSheaf f).obj.obj (op U)) :
    Presieve.Arrows.Compatible ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat) a c := by
  intro i j V b d h
  by_cases hij : i = j
  · subst j
    have hb : b = d := by
      apply Over.OverMorphism.ext
      exact (cancel_mono (a i).left).mp (congrArg Over.Hom.left h)
    subst d
    rfl
  · let _ : IsEmpty V.left := ⟨fun x ↦ by
      have he := congrArg (fun v : V ⟶ E ↦ v.left x) h
      exact Set.disjoint_left.mp (hd hij) ⟨b.left x, rfl⟩ ⟨d.left x, he.symm⟩⟩
    exact relativeFppf_eq_of_isEmpty f V _ _

include hc hd in
/-- Independent branch classes assemble uniquely on the whole original source. -/
theorem disjointSection_existsUnique
    (c : ι → (relativeFppfSheaf f).obj.obj (op U)) :
    ∃! v : (relativeFppfSheaf f).obj.obj (op E),
      ∀ i, (relativeFppfSheaf f).obj.map (a i).op v = c i := by
  have hsheaf := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hsheaf
  have h := hsheaf.isSheafFor _ (disjointSection_covering p a hc)
  rw [Presieve.isSheafFor_arrows_iff] at h
  exact h c (disjointSection_compatible f a hd c)

end FLT.Mazur.SchemePicard
