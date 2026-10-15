/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleNilpotentLift

/-!
# Etale infinitesimal lifts over an unchanged coefficient scheme

The whole scheme lift is a morphism over the original base. Its construction
is natural under compatible maps of infinitesimal tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EtaleNilpotentOverLift
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {T₀ T Y Z : Over S} (i : T₀ ⟶ T)
  [IsClosedImmersion i.left] (hi : IsNilpotent i.left.ker)
  (g : Y ⟶ Z) [Etale g.left] (a : T₀ ⟶ Y) (v : T ⟶ Z) (ha : i ≫ v = a ≫ g)

include hi ha in
/-- The unique whole lift is over the original coefficient scheme. -/
theorem existsUnique_lift : ∃! b : T ⟶ Y, i ≫ b = a ∧ b ≫ g = v := by
  obtain ⟨b, hb, hu⟩ := EtaleNilpotentLift.existsUnique_lift i.left hi g.left a.left v.left
    (congrArg Over.Hom.left ha)
  have hbase : b ≫ Y.hom = T.hom := by
    rw [← Over.w g, ← Category.assoc, hb.2, Over.w v]
  refine ⟨Over.homMk b hbase, ⟨?_, ?_⟩, ?_⟩
  · exact Over.OverMorphism.ext hb.1
  · exact Over.OverMorphism.ext hb.2
  · intro b' hb'
    apply Over.OverMorphism.ext
    exact hu b'.left ⟨congrArg Over.Hom.left hb'.1, congrArg Over.Hom.left hb'.2⟩

/-- The canonical infinitesimal lift over the unchanged base. -/
def lift : T ⟶ Y := (existsUnique_lift i hi g a v ha).choose

/-- The complete given arrow is retained on the original closed test. -/
@[reassoc]
theorem inclusion_lift : i ≫ lift i hi g a v ha = a :=
  (existsUnique_lift i hi g a v ha).choose_spec.1.1

/-- The complete given base arrow is retained on the thickened test. -/
@[reassoc]
theorem lift_base : lift i hi g a v ha ≫ g = v :=
  (existsUnique_lift i hi g a v ha).choose_spec.1.2

/-- Uniqueness identifies any constructed lift with the canonical one. -/
theorem lift_eq (b : T ⟶ Y) (hb : i ≫ b = a) (hbg : b ≫ g = v) :
    lift i hi g a v ha = b :=
  ((existsUnique_lift i hi g a v ha).choose_spec.2 b ⟨hb, hbg⟩).symm

variable {U₀ U : Over S} (j : U₀ ⟶ U) [IsClosedImmersion j.left]
  (hj : IsNilpotent j.left.ker) (s₀ : U₀ ⟶ T₀) (s : U ⟶ T) (hs : j ≫ s = s₀ ≫ i)

/-- Compatible changes of the whole test commute with the constructed lift. -/
theorem naturality :
    lift j hj g (s₀ ≫ a) (s ≫ v) (by
      rw [← Category.assoc, hs, Category.assoc, ha, Category.assoc]) =
      s ≫ lift i hi g a v ha := by
  apply lift_eq
  · rw [← Category.assoc, hs, Category.assoc, inclusion_lift]
  · rw [Category.assoc, lift_base]

end FLT.Mazur.EtaleNilpotentOverLift
