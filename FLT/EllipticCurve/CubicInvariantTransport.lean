/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionQuotient
/-! # Transport of coordinate invariants along equivariant affine isomorphisms

The coordinate pullback is constructed from the fully faithful affine spectrum
functor. A commuting scheme action induces a commuting coordinate action,
and the resulting algebra isomorphism restricts to the fixed subalgebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Pullback of coordinates along an isomorphism between presented affine schemes. -/
def affineCoordinateIso (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (X Y : Over (Spec (.of R)))
    (a : X ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R A)))
    (b : Y ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R B))) (e : X ≅ Y) : B ≃ₐ[R] A :=
  CommAlgCat.algEquivOfIso
    ((algSpec.fullyFaithful (R := .of R)).preimageIso ((a.symm.trans e).trans b)).unop

theorem affineCoordinateIso_spec (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (X Y : Over (Spec (.of R)))
    (a : X ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R A)))
    (b : Y ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R B))) (e : X ≅ Y) :
    (algSpec (.of R)).map (CommAlgCat.ofHom (affineCoordinateIso A B X Y a b e).toAlgHom).op =
      a.inv ≫ e.hom ≫ b.hom := by
  change (algSpec (.of R)).map ((algSpec.fullyFaithful (R := .of R)).preimage
    (a.inv ≫ e.hom ≫ b.hom)) = _
  exact (algSpec.fullyFaithful (R := .of R)).map_preimage _


/-- Pullback of coordinates intertwines commuting affine actions. -/
theorem affineCoordinateIso_commutes (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (X Y : Over (Spec (.of R)))
    (a : X ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R A)))
    (b : Y ≅ (algSpec (.of R)).obj (op (CommAlgCat.of R B))) (e : X ≅ Y)
    (σ : Aut X) (τ : Aut Y) (h : σ.inv ≫ e.hom = e.hom ≫ τ.inv) :
    (affineCoordinateIso A B X Y a b e).toAlgHom.comp
        (affineCoordinateAut B Y b τ).toAlgHom =
      (affineCoordinateAut A X a σ).toAlgHom.comp
        (affineCoordinateIso A B X Y a b e).toAlgHom := by
  let F := (affineCoordinateIso A B X Y a b e).toAlgHom
  let S := (affineCoordinateAut A X a σ).toAlgHom
  let T := (affineCoordinateAut B Y b τ).toAlgHom
  have hh : (CommAlgCat.ofHom (F.comp T)).op = (CommAlgCat.ofHom (S.comp F)).op := by
    apply (algSpec.fullyFaithful (R := .of R)).map_injective
    change (algSpec (.of R)).map ((CommAlgCat.ofHom F).op ≫ (CommAlgCat.ofHom T).op) =
      (algSpec (.of R)).map ((CommAlgCat.ofHom S).op ≫ (CommAlgCat.ofHom F).op)
    rw [Functor.map_comp, Functor.map_comp]
    simp only [F, S, T, affineCoordinateIso_spec, affineCoordinateAut_spec,
      Category.assoc, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using
      congrArg (fun f => a.inv ≫ f ≫ b.hom) h.symm
  exact congrArg (fun f : op (CommAlgCat.of R A) ⟶ op (CommAlgCat.of R B) => f.unop.hom) hh


/-- An equivariant algebra isomorphism restricts to an isomorphism of invariant algebras. -/
def invariantAlgebraEquiv {A B : Type u} {G : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Group G]
    [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G R A] [SMulCommClass G R B]
    (e : A ≃ₐ[R] B) (h : ∀ (g : G) (x : A), e (g • x) = g • e x) :
    FixedPoints.subalgebra R A G ≃ₐ[R] FixedPoints.subalgebra R B G where
  toFun x := ⟨e x.val, fun g => by
    change g • e x.val = e x.val
    rw [← h, show g • x.val = x.val from x.property g]⟩
  invFun y := ⟨e.symm y.val, fun g => by
    apply e.injective
    rw [h, e.apply_symm_apply]
    exact y.property g⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  commutes' r := Subtype.ext (e.commutes r)

end WeierstrassCurve.CubicCharts

