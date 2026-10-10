/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineIsomorphism
public import FLT.Mazur.DualAtlasLineQuotient

/-!
# Retained sublines in a rank-one ambient sheaf

The original inclusion identifies every locally split subline with the
ambient line. The comparison between two retained sources is unique and
preserves their original inclusions, including on nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.DualAtlasLineQuotient
open FCurve SplitLineAffineNeighborhood
variable {X : Scheme.{u}} {M : X.Modules} (hM : LocallyFreeRankOne M)

/-- The entire ambient line, with its original identity inclusion. -/
def wholeLine : Line M where
  source := M
  rankOne := hM
  inclusion := 𝟙 M
  locallySplit x := ⟨⊤, trivial, by rw [CategoryTheory.Functor.map_id]; infer_instance⟩

include hM in
/-- Every original inclusion into a rank-one ambient sheaf is invertible. -/
theorem Line.inclusion_isIso (a : Line M) : IsIso a.inclusion :=
  a.locallySplit.isIso a.inclusion a.rankOne hM

/-- The source comparison is constructed from the two actual inclusions. -/
def Line.sourceIso (a b : Line M) : a.source ≅ b.source := by
  let _ := a.inclusion_isIso hM
  let _ := b.inclusion_isIso hM
  exact asIso a.inclusion ≪≫ (asIso b.inclusion).symm

/-- The comparison retains the entire original inclusion. -/
lemma Line.sourceIso_inclusion (a b : Line M) :
    (a.sourceIso hM b).hom ≫ b.inclusion = a.inclusion := by
  let _ := a.inclusion_isIso hM
  let _ := b.inclusion_isIso hM
  simp only [Line.sourceIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

include hM in
/-- There is exactly one isomorphism of retained sources preserving their inclusions. -/
theorem Line.existsUnique_sourceIso (a b : Line M) :
    ∃! e : a.source ≅ b.source, e.hom ≫ b.inclusion = a.inclusion := by
  let _ := b.inclusion_isIso hM
  refine ⟨a.sourceIso hM b, a.sourceIso_inclusion hM b, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_mono b.inclusion).mp
  exact he.trans (a.sourceIso_inclusion hM b).symm

include hM in
/-- Any two original sublines represent the same class in a rank-one ambient bundle. -/
theorem lineSetoid_rankOne (a b : Line M) : (lineSetoid M).r a b :=
  ⟨a.sourceIso hM b, a.sourceIso_inclusion hM b⟩

/-- The actual quotient of retained line inclusions has a canonical unique element. -/
@[instance_reducible] def rankOneLineQuotientUnique : Unique (Quotient (lineSetoid M)) where
  default := Quotient.mk _ (wholeLine hM)
  uniq a := by
    induction a using Quotient.inductionOn with | h a =>
      exact Quotient.sound (lineSetoid_rankOne hM a (wholeLine hM))

end FLT.Mazur.DualAtlasLineQuotient
