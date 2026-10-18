/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Specified sections through three compatible subgroup comparisons

Compose section equalities on abstract subgroup carriers, so applications to
normalization and relabeling need not unfold geometric group constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {n : ℕ} {E F G K : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {A : G.FiniteSubgroup n} {B : K.FiniteSubgroup n}
  (a : CompatibleIso H J) (b : CompatibleIso J A) (c : CompatibleIso A B)

/-- Three full comparisons carry the original specified section to the final specified section. -/
theorem CompatibleIso.subgroup_section_trans_three
    (s : 𝟙_ (Over S) ⟶ H.carrier) (t : 𝟙_ (Over S) ⟶ J.carrier)
    (u : 𝟙_ (Over S) ⟶ A.carrier) (v : 𝟙_ (Over S) ⟶ B.carrier)
    (ha : s ≫ a.subgroup.hom = t) (hb : t ≫ b.subgroup.hom = u)
    (hc : u ≫ c.subgroup.hom = v) :
    s ≫ (a.trans (b.trans c)).subgroup.hom = v := by
  change s ≫ (a.subgroup.hom ≫ b.subgroup.hom ≫ c.subgroup.hom) = v
  rw [← Category.assoc, ha, ← Category.assoc, hb, hc]

/-- Equality of full comparisons transfers a section equation without unfolding comparisons. -/
theorem CompatibleIso.subgroup_section_iso_congr (d : CompatibleIso H J)
    (s : 𝟙_ (Over S) ⟶ H.carrier) (t : 𝟙_ (Over S) ⟶ J.carrier)
    (had : a = d) (hd : s ≫ d.subgroup.hom = t) : s ≫ a.subgroup.hom = t := by
  rw [had]
  exact hd

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
