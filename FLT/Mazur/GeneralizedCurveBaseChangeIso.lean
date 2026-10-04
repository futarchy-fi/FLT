/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChange
public import FLT.Mazur.GeneralizedCurvePullbackCoherence

/-!
# Comparison isomorphisms for generalized-curve base change

The canonical curve and group comparisons lift to the full DR category.
Their naturality gives comparisons between the actual base-change functors.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {S T U : Scheme}

/-- Compatible curve and group isomorphisms give an isomorphism of DR objects. -/
def isoMk {E F : GeneralizedEllipticCurve S}
    (c : E.curve ≅ F.curve) (g : E.group ≅ F.group) [IsMonHom g.hom]
    (hi : E.inclusion ≫ c.hom = g.hom ≫ F.inclusion)
    (ha : E.act ≫ c.hom = (g.hom ⊗ₘ c.hom) ≫ F.act) : E ≅ F where
  hom := { curve := c.hom, group := g.hom, inclusion := hi, action := ha }
  inv :=
    { curve := c.inv
      group := g.inv
      inclusion := by
        apply (cancel_mono c.hom).mp
        simp only [Category.assoc, c.inv_hom_id, Category.comp_id]
        rw [hi, ← Category.assoc, g.inv_hom_id, Category.id_comp]
      action := by
        apply (cancel_mono c.hom).mp
        simp only [Category.assoc, c.inv_hom_id, Category.comp_id]
        rw [ha, ← Category.assoc, tensorHom_comp_tensorHom]
        simp }
  hom_inv_id := Hom.ext c.hom_inv_id g.hom_inv_id
  inv_hom_id := Hom.ext c.inv_hom_id g.inv_hom_id

/-- Pulling back a full DR object along the identity recovers that object. -/
def baseChangeIdIso (E : GeneralizedEllipticCurve S) : E.baseChange (𝟙 S) ≅ E := by
  letI : IsMonHom E.pullbackGroupIdIso.hom :=
    { one_hom := E.pullback_id_one, mul_hom := E.pullback_id_mul }
  exact isoMk E.pullbackCurveIdIso E.pullbackGroupIdIso
    (by simpa only [baseChange_inclusion] using E.pullback_id_inclusion)
    E.pullback_id_action

/-- Direct and iterated base change agree as full DR objects. -/
def baseChangeCompIso (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (h : U ⟶ T) :
    E.baseChange (h ≫ g) ≅ (E.baseChange g).baseChange h := by
  letI : IsMonHom (E.pullbackGroupCompIso g h).hom :=
    { one_hom := E.pullback_comp_one g h, mul_hom := E.pullback_comp_mul g h }
  exact isoMk (E.pullbackCurveCompIso g h) (E.pullbackGroupCompIso g h)
    (by simpa only [baseChange_inclusion, pullbackInclusion] using E.pullback_comp_inclusion g h)
    (E.pullback_comp_action g h)

/-- The identity comparison is natural in all compatible DR morphisms. -/
def baseChangeId : baseChangeFunctor (𝟙 S) ≅ 𝟭 (GeneralizedEllipticCurve S) :=
  NatIso.ofComponents baseChangeIdIso fun f ↦
    (forgetCurve.map_injective (pullback_id_natural _ f))

/-- The composition comparison is natural in all compatible DR morphisms. -/
def baseChangeComp (g : T ⟶ S) (h : U ⟶ T) :
    baseChangeFunctor (h ≫ g) ≅ baseChangeFunctor g ⋙ baseChangeFunctor h :=
  NatIso.ofComponents (fun E ↦ E.baseChangeCompIso g h) fun f ↦
    (forgetCurve.map_injective (pullback_comp_natural _ g h f))

end FLT.Mazur.GeneralizedEllipticCurve
