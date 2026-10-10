/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGeneratorTransport

/-!
# Compatible isomorphisms of finite subgroup data

An isomorphism preserves the full generalized curve and the subgroup group
scheme, with its actual inclusion into the curve. Identity, inverse and
composition are constructed and satisfy the groupoid laws.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

variable {S : Scheme} {n : ℕ} {E F G K : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)

/-- An isomorphism of the curve and subgroup preserving the actual inclusion. -/
structure CompatibleIso where
  /-- The full generalized-curve isomorphism. -/
  curve : E ≅ F
  /-- The isomorphism of subgroup schemes over the base. -/
  subgroup : H.carrier ≅ J.carrier
  /-- The subgroup isomorphism preserves the group law. -/
  [isMonHom : IsMonHom subgroup.hom]
  /-- Compatibility with the actual whole-curve inclusions. -/
  compatible : H.curveMap ≫ curve.hom.curve = subgroup.hom ≫ J.curveMap

attribute [instance] CompatibleIso.isMonHom

/-- Equality is determined by the two geometric isomorphisms. -/
@[ext]
theorem CompatibleIso.ext {a b : CompatibleIso H J}
    (hc : a.curve = b.curve) (hs : a.subgroup = b.subgroup) : a = b := by
  cases a
  cases b
  cases hc
  cases hs
  rfl

/-- Identity preserves the subgroup inclusion. -/
def CompatibleIso.refl : CompatibleIso H H where
  curve := Iso.refl E
  subgroup := Iso.refl H.carrier
  isMonHom := inferInstanceAs (IsMonHom (𝟙 H.carrier))
  compatible := by
    change H.curveMap ≫ 𝟙 E.curve = (𝟙 H.carrier) ≫ H.curveMap
    simp

variable {H J} {A : G.FiniteSubgroup n} {B : K.FiniteSubgroup n}

/-- Inverting both geometric isomorphisms preserves inclusion compatibility. -/
def CompatibleIso.symm (a : CompatibleIso H J) : CompatibleIso J H where
  curve := a.curve.symm
  subgroup := a.subgroup.symm
  isMonHom := inferInstanceAs (IsMonHom a.subgroup.inv)
  compatible := by
    have : IsIso a.curve.hom.curve :=
      inferInstanceAs (IsIso (forgetCurve.map a.curve.hom))
    apply (cancel_mono a.curve.hom.curve).mp
    have hc : a.curve.inv.curve ≫ a.curve.hom.curve = 𝟙 F.curve :=
      congrArg Hom.curve a.curve.inv_hom_id
    change (J.curveMap ≫ a.curve.inv.curve) ≫ a.curve.hom.curve =
      (a.subgroup.inv ≫ H.curveMap) ≫ a.curve.hom.curve
    rw [Category.assoc, hc, Category.comp_id, Category.assoc, a.compatible,
      ← Category.assoc, a.subgroup.inv_hom_id, Category.id_comp]

/-- Compose the full curve and subgroup isomorphisms. -/
def CompatibleIso.trans (a : CompatibleIso H J) (b : CompatibleIso J A) :
    CompatibleIso H A where
  curve := a.curve ≪≫ b.curve
  subgroup := a.subgroup ≪≫ b.subgroup
  isMonHom := inferInstanceAs (IsMonHom (a.subgroup.hom ≫ b.subgroup.hom))
  compatible := by
    change H.curveMap ≫ (a.curve.hom.curve ≫ b.curve.hom.curve) =
      (a.subgroup.hom ≫ b.subgroup.hom) ≫ A.curveMap
    rw [← Category.assoc, a.compatible, Category.assoc, b.compatible, Category.assoc]

/-- Left identity for compatible isomorphisms. -/
theorem CompatibleIso.refl_trans (a : CompatibleIso H J) :
    (CompatibleIso.refl H).trans a = a := by
  apply CompatibleIso.ext <;> simp [CompatibleIso.trans, CompatibleIso.refl]

/-- Right identity for compatible isomorphisms. -/
theorem CompatibleIso.trans_refl (a : CompatibleIso H J) :
    a.trans (CompatibleIso.refl J) = a := by
  apply CompatibleIso.ext <;> simp [CompatibleIso.trans, CompatibleIso.refl]

/-- Associativity is inherited from the two geometric isomorphisms. -/
theorem CompatibleIso.trans_assoc (a : CompatibleIso H J) (b : CompatibleIso J A)
    (d : CompatibleIso A B) : (a.trans b).trans d = a.trans (b.trans d) := by
  apply CompatibleIso.ext <;> simp [CompatibleIso.trans]

/-- A compatible inverse is a right inverse. -/
theorem CompatibleIso.trans_symm (a : CompatibleIso H J) :
    a.trans a.symm = CompatibleIso.refl H := by
  apply CompatibleIso.ext <;> simp [CompatibleIso.trans, CompatibleIso.symm, CompatibleIso.refl]

/-- A compatible inverse is a left inverse. -/
theorem CompatibleIso.symm_trans (a : CompatibleIso H J) :
    a.symm.trans a = CompatibleIso.refl J := by
  apply CompatibleIso.ext <;> simp [CompatibleIso.trans, CompatibleIso.symm, CompatibleIso.refl]

/-- The constructed compatible isomorphism transports actual Cartier generators. -/
theorem CompatibleIso.cartierGenerator (a : CompatibleIso H J)
    {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P) :
    J.IsCartierGenerator (P ≫ a.subgroup.hom) :=
  hP.transport H J a.curve a.subgroup a.compatible

/-- Compatible isomorphism is an equivalence relation on finite subgroup data. -/
def compatibleIsoSetoid (S : Scheme) (n : ℕ) :
    Setoid (Σ E : GeneralizedEllipticCurve S, E.FiniteSubgroup n) where
  r a b := Nonempty (CompatibleIso a.2 b.2)
  iseqv := ⟨fun a ↦ ⟨CompatibleIso.refl a.2⟩,
    fun ⟨a⟩ ↦ ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ ↦ ⟨a.trans b⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
