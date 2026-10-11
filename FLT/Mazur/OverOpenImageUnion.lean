/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Open image unions over an unchanged base

The union retains the original relative charts and their actual covering arrows.
Any relative map whose image lies in the union factors uniquely through it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {T : Over S} {ι : Type} {V : ι → Over S}
  (c : ∀ i, V i ⟶ T) [∀ i, IsOpenImmersion (c i).left]

/-- The union of relative open images, with its original base morphism. -/
def overOpenImageUnion : Over S :=
  Over.mk ((openImageUnion (fun i ↦ (c i).left)).ι ≫ T.hom)

/-- The original open inclusion of the union into the test. -/
def overOpenImageUnionι : overOpenImageUnion c ⟶ T :=
  Over.homMk (openImageUnion (fun i ↦ (c i).left)).ι rfl

instance overOpenImageUnionι_isOpenImmersion :
    IsOpenImmersion (overOpenImageUnionι c).left := inferInstanceAs
      (IsOpenImmersion (openImageUnion (fun i ↦ (c i).left)).ι)

instance overOpenImageUnionι_mono : Mono (overOpenImageUnionι c) :=
  Over.mono_of_mono_left _

/-- Each original relative chart embeds into the union. -/
def overOpenImageUnionMap (i : ι) : V i ⟶ overOpenImageUnion c :=
  Over.homMk (openImageUnionMap (fun i ↦ (c i).left) i) (by
    change _ ≫ (_ ≫ T.hom) = _
    rw [← Category.assoc, openImageUnionMap_fac, Over.w])

@[reassoc (attr := simp)]
theorem overOpenImageUnionMap_fac (i : ι) :
    overOpenImageUnionMap c i ≫ overOpenImageUnionι c = c i :=
  Over.OverMorphism.ext (openImageUnionMap_fac _ _)

/-- The original charts cover the union in the relative fppf topology. -/
theorem overOpenImageUnion_cover :
    Sieve.ofArrows V (overOpenImageUnionMap c) ∈
      (Scheme.fppfTopology.over S) (overOpenImageUnion c) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _
      (openImageUnionCover (fun i ↦ (c i).left)).mem₀)

/-- Image containment produces the unique relative factorization through the open union. -/
theorem overOpenImageUnion_lift {U : Over S} (b : U ⟶ T)
    (hb : Set.range b.left ⊆ (openImageUnion (fun i ↦ (c i).left) : Set T.left)) :
    ∃! k : U ⟶ overOpenImageUnion c, k ≫ overOpenImageUnionι c = b := by
  let k := IsOpenImmersion.lift (overOpenImageUnionι c).left b.left (by
    change Set.range b.left ⊆ Set.range (openImageUnion (fun i ↦ (c i).left)).ι
    rw [Scheme.Opens.range_ι]
    exact hb)
  have hk : k ≫ (overOpenImageUnionι c).left = b.left :=
    IsOpenImmersion.lift_fac _ _ _
  let q : U ⟶ overOpenImageUnion c := Over.homMk k (by
    change k ≫ ((overOpenImageUnionι c).left ≫ T.hom) = U.hom
    rw [← Category.assoc, hk, Over.w])
  have hq : q ≫ overOpenImageUnionι c = b := Over.OverMorphism.ext hk
  exact ⟨q, hq, fun l hl ↦ (cancel_mono (overOpenImageUnionι c)).mp (hl.trans hq.symm)⟩

end FLT.Mazur
