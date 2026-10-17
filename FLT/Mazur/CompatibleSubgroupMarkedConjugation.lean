/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Marked sections through conjugated compatible comparisons

Section transport is proved on abstract subgroup and curve objects, keeping
geometric definitions sealed when this result is applied to atlas relations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E F G K : GeneralizedEllipticCurve S} {n : ℕ}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {A : G.FiniteSubgroup n} {B : K.FiniteSubgroup n}
  (a : CompatibleIso H J) (b : CompatibleIso H A) (c : CompatibleIso A B)

/-- Conjugation retains prescribed sections of the actual subgroup carriers. -/
theorem CompatibleIso.subgroup_section_conjugate
    (s : 𝟙_ (Over S) ⟶ J.carrier) (t : 𝟙_ (Over S) ⟶ H.carrier)
    (u : 𝟙_ (Over S) ⟶ A.carrier) (v : 𝟙_ (Over S) ⟶ B.carrier)
    (ht : t ≫ a.subgroup.hom = s) (hb : t ≫ b.subgroup.hom = u)
    (hc : u ≫ c.subgroup.hom = v) :
    s ≫ (a.symm.trans (b.trans c)).subgroup.hom = v := by
  change s ≫ (a.subgroup.inv ≫ b.subgroup.hom ≫ c.subgroup.hom) = v
  rw [← ht]
  simp only [Category.assoc, ← Category.assoc a.subgroup.hom,
    a.subgroup.hom_inv_id, Category.id_comp]
  rw [← Category.assoc, hb, hc]

/-- The same conjugation retains prescribed auxiliary sections on the full curve group. -/
theorem CompatibleIso.group_section_conjugate
    (s : 𝟙_ (Over S) ⟶ F.group) (t : 𝟙_ (Over S) ⟶ E.group)
    (u : 𝟙_ (Over S) ⟶ G.group) (v : 𝟙_ (Over S) ⟶ K.group)
    (ht : t ≫ a.curve.hom.group = s) (hb : t ≫ b.curve.hom.group = u)
    (hc : u ≫ c.curve.hom.group = v) :
    s ≫ (a.symm.trans (b.trans c)).curve.hom.group = v := by
  have hi : a.curve.hom.group ≫ a.curve.inv.group = 𝟙 _ :=
    congrArg Hom.group a.curve.hom_inv_id
  change s ≫ (a.curve.inv.group ≫ b.curve.hom.group ≫ c.curve.hom.group) = v
  rw [← ht]
  simp only [Category.assoc, ← Category.assoc a.curve.hom.group, hi, Category.id_comp]
  rw [← Category.assoc, hb, hc]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
