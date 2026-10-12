/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Iterating full relation restrictions

Restriction in two stages retains exactly the original arrows with endpoints in
the final source. Compatibility also survives an isomorphism of relation schemes
which preserves both endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {A X Y Z : Scheme.{u}} (p q : A ⟶ X) (k : Y ⟶ X) (l : Z ⟶ Y)

/-- An arrow restricted to the final source is still an original arrow in the first restriction. -/
def compositeToFirst : doubleDomain p q (l ≫ k) ⟶ doubleDomain p q k :=
  lift p q k (arrow p q (l ≫ k)) (fst p q (l ≫ k) ≫ l) (snd p q (l ≫ k) ≫ l)
    (by rw [Category.assoc, arrow_fst]) (by rw [Category.assoc, arrow_snd])

@[reassoc]
theorem compositeToFirst_fst : compositeToFirst p q k l ≫ fst p q k =
    fst p q (l ≫ k) ≫ l := lift_fst _ _ _ _ _ _ _ _

@[reassoc]
theorem compositeToFirst_snd : compositeToFirst p q k l ≫ snd p q k =
    snd p q (l ≫ k) ≫ l := lift_snd _ _ _ _ _ _ _ _

/-- Two successive full restrictions impose exactly the direct original endpoint equation. -/
theorem composite_compatible_iff (v : Γ(Z, ⊤)) :
    v ∈ compatibleFunctions (fst p q (l ≫ k)) (snd p q (l ≫ k)) ↔
      v ∈ compatibleFunctions (fst (fst p q k) (snd p q k) l)
        (snd (fst p q k) (snd p q k) l) := by
  constructor
  · intro hv
    apply compatible_on_arrow p q (l ≫ k)
      (arrow (fst p q k) (snd p q k) l ≫ arrow p q k)
      (fst (fst p q k) (snd p q k) l) (snd (fst p q k) (snd p q k) l)
      (s := ⟨v, hv⟩)
    · rw [Category.assoc, arrow_fst, arrow_fst_assoc]
    · rw [Category.assoc, arrow_snd, arrow_snd_assoc]
  · intro hv
    exact compatible_on_arrow (fst p q k) (snd p q k) l (compositeToFirst p q k l)
      (fst p q (l ≫ k)) (snd p q (l ≫ k))
      (compositeToFirst_fst p q k l) (compositeToFirst_snd p q k l) ⟨v, hv⟩

/-- Iterating restrictions changes no original compatible regular function. -/
def compositeFunctionEquiv : compatibleFunctions (fst p q (l ≫ k)) (snd p q (l ≫ k)) ≃+*
    compatibleFunctions (fst (fst p q k) (snd p q k) l)
      (snd (fst p q k) (snd p q k) l) :=
  RingEquiv.subringCongr (SetLike.ext fun v ↦ composite_compatible_iff p q k l v)

variable {B : Scheme.{u}} (r s : B ⟶ X) (i : B ≅ A)
  (hi₁ : i.hom ≫ p = r) (hi₂ : i.hom ≫ q = s)

include hi₁ hi₂ in
/-- Full restriction compatibility is unchanged by an endpoint-preserving relation isomorphism. -/
theorem relationIso_compatible_iff (v : Γ(Y, ⊤)) :
    v ∈ compatibleFunctions (fst p q k) (snd p q k) ↔
      v ∈ compatibleFunctions (fst r s k) (snd r s k) := by
  constructor
  · intro hv
    apply compatible_on_arrow p q k (arrow r s k ≫ i.hom)
      (fst r s k) (snd r s k) (s := ⟨v, hv⟩)
    · rw [Category.assoc, hi₁, arrow_fst]
    · rw [Category.assoc, hi₂, arrow_snd]
  · intro hv
    have h₁ : i.inv ≫ r = p := by rw [← hi₁, Iso.inv_hom_id_assoc]
    have h₂ : i.inv ≫ s = q := by rw [← hi₂, Iso.inv_hom_id_assoc]
    apply compatible_on_arrow r s k (arrow p q k ≫ i.inv)
      (fst p q k) (snd p q k) (s := ⟨v, hv⟩)
    · rw [Category.assoc, h₁, arrow_fst]
    · rw [Category.assoc, h₂, arrow_snd]

/-- Relation-coordinate transport retains the actual regular function. -/
def relationIsoFunctionEquiv : compatibleFunctions (fst p q k) (snd p q k) ≃+*
    compatibleFunctions (fst r s k) (snd r s k) :=
  RingEquiv.subringCongr
    (SetLike.ext fun v ↦ relationIso_compatible_iff p q k r s i hi₁ hi₂ v)

end FLT.Mazur.SchemeRelationRestriction
