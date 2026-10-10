/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionScheme

/-!
# The torsion equalizer inherits its original commutative group structure

The represented torsion functor is a presheaf of actual subgroups of the
original group of sections. Representability transfers those operations to
the already constructed equalizer, and its inclusion preserves them.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry MonObj Opposite

namespace FLT.Mazur.GroupTorsionScheme

variable {S : Scheme} (E : Over S) [CommGrpObj E] (n : ℕ)

/-- The torsion subgroup of the original group-valued points. -/
def pointSubgroup (U : Over S) : Subgroup (U ⟶ E) where
  carrier := {f | f ^ n = 1}
  one_mem' := one_pow n
  mul_mem' {a b} hf hg := by
    change a ^ n = 1 at hf
    change b ^ n = 1 at hg
    change (a * b) ^ n = 1
    rw [mul_pow, hf, hg, _root_.one_mul]
  inv_mem' {a} hf := by
    change a ^ n = 1 at hf
    change a⁻¹ ^ n = 1
    rw [inv_pow, hf, inv_one]

/-- Torsion subgroups form a presheaf of commutative groups. -/
def pointFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat where
  obj U := .of (pointSubgroup E n U.unop)
  map f := CommGrpCat.ofHom
    { toFun := fun P ↦ ⟨f.unop ≫ P.val, by
        have hP : P.val ^ n = 1 := P.property
        change (f.unop ≫ P.val) ^ n = 1
        rw [← MonObj.comp_pow, hP, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' P Q := Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id U := CommGrpCat.hom_ext (MonoidHom.ext fun P ↦
    Subtype.ext (Category.id_comp P.val))
  map_comp f g := CommGrpCat.hom_ext (MonoidHom.ext fun P ↦
    Subtype.ext (Category.assoc _ _ _))

/-- The original torsion equalizer represents its subgroup-valued functor. -/
def pointRepresentable : (pointFunctor E n ⋙ forget _).RepresentableBy (scheme E n) where
  homEquiv := representation E n _
  homEquiv_comp f g := Subtype.ext (Category.assoc f g (inclusion E n))

/-- The original equalizer, rather than a replacement model, is a commutative group scheme. -/
instance commGrpObj : CommGrpObj (scheme E n) :=
  CommGrpObj.ofRepresentableBy (scheme E n) (pointFunctor E n) (pointRepresentable E n)

/-- The actual inclusion into the original group preserves its group operations. -/
instance inclusion_isMonHom : IsMonHom (inclusion E n) where
  one_hom := by
    change lift E n 1 (one_pow n) ≫ inclusion E n = η[E]
    rw [lift_inclusion]
    simp only [CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp]
  mul_hom := by
    change lift E n ((fst _ _ ≫ inclusion E n) * (snd _ _ ≫ inclusion E n))
      (by simp only [mul_pow, ← MonObj.comp_pow, inclusion_pow, MonObj.comp_one,
        _root_.one_mul]) ≫ inclusion E n = (inclusion E n ⊗ₘ inclusion E n) ≫ μ[E]
    rw [lift_inclusion, CategoryTheory.Hom.mul_def, lift_fst_comp_snd_comp]

/-- The actual torsion inclusion is a monomorphism. -/
instance inclusion_mono : Mono (inclusion E n) :=
  inferInstanceAs (Mono (equalizer.ι (powerMap E n) (1 : E ⟶ E)))

/-- Factoring an original homomorphism through the torsion equation preserves multiplication. -/
def liftMarking {U : Over S} {A : Type} [Monoid A] (φ : A →* (U ⟶ E))
    (hφ : ∀ a, φ a ^ n = 1) : A →* (U ⟶ scheme E n) where
  toFun a := lift E n (φ a) (hφ a)
  map_one' := by
    apply (cancel_mono (inclusion E n)).mp
    rw [lift_inclusion, MonObj.one_comp, map_one]
  map_mul' a b := by
    apply (cancel_mono (inclusion E n)).mp
    rw [lift_inclusion, MonObj.mul_comp, lift_inclusion, lift_inclusion, map_mul]

/-- Every lifted marking recovers the original values under the torsion inclusion. -/
@[reassoc (attr := simp)] theorem liftMarking_inclusion {U : Over S} {A : Type} [Monoid A]
    (φ : A →* (U ⟶ E)) (hφ : ∀ a, φ a ^ n = 1) (a : A) :
    liftMarking E n φ hφ a ≫ inclusion E n = φ a := lift_inclusion E n (φ a) (hφ a)

end FLT.Mazur.GroupTorsionScheme
