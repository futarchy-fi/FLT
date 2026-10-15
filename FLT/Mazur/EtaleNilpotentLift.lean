/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleNilpotentGlue
public import FLT.Mazur.EtaleNilpotentLocalLift

/-!
# Whole scheme lifts across nilpotent closed immersions

Etale morphisms have unique infinitesimal lifts for arbitrary schemes.
Affine neighborhoods are constructed point by point and glued using uniqueness;
no affineness of any of the four original schemes is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleNilpotentLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T₀ T Y Z : Scheme} (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker) (g : Y ⟶ Z) [Etale g]
  (a : T₀ ⟶ Y) (v : T ⟶ Z) (ha : i ≫ v = a ≫ g)

include hi ha in
/-- Etale targets have unique whole scheme lifts across any nilpotent closed immersion. -/
theorem existsUnique_lift : ∃! b : T ⟶ Y, i ≫ b = a ∧ b ≫ g = v := by
  choose W hW hx b hb hv using EtaleNilpotentLocalLift.exists_lift i hi g a v ha
  let 𝒰 : T.OpenCover := {
    I₀ := T, X x := (W x).toScheme, f x := (W x).ι,
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ⟨x, by simpa using hx x⟩, inferInstance⟩ }
  apply EtaleNilpotentGlue.existsUnique_lift i hi g a v 𝒰 b _ hv
  intro x
  change pullback.fst (W x).ι i ≫ b x = pullback.snd _ _ ≫ a
  let H := isPullback_morphismRestrict i (W x)
  apply (cancel_epi H.isoPullback.hom).mp
  rw [← Category.assoc, ← Category.assoc, H.isoPullback_hom_fst,
    H.isoPullback_hom_snd]
  exact hb x

/-- The whole lift constructed from affine local lifts and scheme gluing. -/
def lift : T ⟶ Y := (existsUnique_lift i hi g a v ha).choose

/-- The lift retains the complete lower-order arrow. -/
@[reassoc]
theorem inclusion_lift : i ≫ lift i hi g a v ha = a :=
  (existsUnique_lift i hi g a v ha).choose_spec.1.1

/-- The lift retains the complete coefficient morphism. -/
@[reassoc]
theorem lift_base : lift i hi g a v ha ≫ g = v :=
  (existsUnique_lift i hi g a v ha).choose_spec.1.2

/-- The construction is independent of every local choice. -/
theorem lift_eq (b : T ⟶ Y) (hb : i ≫ b = a) (hbg : b ≫ g = v) :
    lift i hi g a v ha = b :=
  ((existsUnique_lift i hi g a v ha).choose_spec.2 b ⟨hb, hbg⟩).symm

end FLT.Mazur.EtaleNilpotentLift
