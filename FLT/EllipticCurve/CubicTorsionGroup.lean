/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionFinite

/-! # The represented torsion kernel as a finite commutative group scheme -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- The n-torsion subgroup of the group of points with arbitrary scheme source. -/
abbrev torsionPointGroup (n : ℕ) (X : Over (Spec (.of R))) :=
  (powMonoidHom n : (X ⟶ groupModel W) →* (X ⟶ groupModel W)).ker

/-- Pullback of torsion points is a group homomorphism. -/
def torsionPointRestriction (n : ℕ) {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    torsionPointGroup W n Y →* torsionPointGroup W n X where
  toFun P := ⟨f ≫ P.1, by
    let h := ((yonedaGrpObj (groupModel W)).map f.op).hom
    change (h P.1) ^ n = 1
    rw [← map_pow, show P.1 ^ n = 1 from P.2, map_one]⟩
  map_one' := Subtype.ext (((yonedaGrpObj (groupModel W)).map f.op).hom.map_one)
  map_mul' P Q := Subtype.ext (((yonedaGrpObj (groupModel W)).map f.op).hom.map_mul P.1 Q.1)

/-- The torsion point functor takes values in commutative groups. -/
def torsionPointFunctor (n : ℕ) : (Over (Spec (.of R)))ᵒᵖ ⥤ CommGrpCat where
  obj X := CommGrpCat.of (torsionPointGroup W n X.unop)
  map f := CommGrpCat.ofHom (torsionPointRestriction W n f.unop)
  map_id X := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro P
    apply Subtype.ext
    exact Category.id_comp P.1
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro P
    apply Subtype.ext
    exact Category.assoc _ _ P.1

/-- The constructed equalizer represents the full commutative-group-valued torsion functor. -/
def torsionPointRepresentable (n : ℕ) :
    (torsionPointFunctor W n ⋙ forget _).RepresentableBy (torsionModel W n) where
  homEquiv {X} := torsionModelPointEquiv W n X
  homEquiv_comp f g := by
    apply Subtype.ext
    exact Category.assoc _ _ _

instance torsionModelCommGrpObj (n : ℕ) : CommGrpObj (torsionModel W n) :=
  CommGrpObj.ofRepresentableBy (torsionModel W n) (torsionPointFunctor W n)
    (torsionPointRepresentable W n)

/-- The representing bijection respects the constructed group laws. -/
def torsionPointMulEquiv (n : ℕ) (X : Over (Spec (.of R))) :
    (X ⟶ torsionModel W n) ≃* torsionPointGroup W n X where
  toEquiv := torsionModelPointEquiv W n X
  map_mul' f g :=
    ((yonedaGrpObjIsoOfRepresentableBy (torsionModel W n)
      (torsionPointFunctor W n ⋙ forget₂ CommGrpCat GrpCat)
      (torsionPointRepresentable W n)).hom.app (op X)).hom.map_mul f g

/-- Multiplication by n is identically zero on the represented torsion group. -/
theorem torsionPoint_pow_eq_one (n : ℕ) {X : Over (Spec (.of R))}
    (f : X ⟶ torsionModel W n) : f ^ n = 1 := by
  apply (torsionPointMulEquiv W n X).injective
  rw [map_pow, map_one]
  exact Subtype.ext ((torsionPointMulEquiv W n X f).property)

instance torsionInclusionIsMonHom (n : ℕ) : IsMonHom (torsionInclusion W n) where
  one_hom := by
    have h := congrArg Subtype.val
      ((torsionPointMulEquiv W n (𝟙_ (Over (Spec (.of R))))).map_one)
    change (1 : 𝟙_ (Over (Spec (.of R))) ⟶ torsionModel W n) ≫
      torsionInclusion W n = (1 : 𝟙_ (Over (Spec (.of R))) ⟶ groupModel W) at h
    simpa [Hom.one_def] using h
  mul_hom := by
    let T := torsionModel W n
    have h := congrArg Subtype.val
      ((torsionPointMulEquiv W n (T ⊗ T)).map_mul (fst T T) (snd T T))
    change ((fst T T) * (snd T T)) ≫ torsionInclusion W n =
      ((fst T T) ≫ torsionInclusion W n) * ((snd T T) ≫ torsionInclusion W n) at h
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    refine h.trans ?_
    congr 1

end WeierstrassCurve.CubicCharts
