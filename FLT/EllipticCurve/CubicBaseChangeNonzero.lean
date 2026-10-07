/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeTorsion
public import FLT.EllipticCurve.CubicNonzeroTorsion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
/-! # Base change of nonzero torsion

The torsion comparison is a cartesian square. Its compatibility with
the zero section identifies the nonzero open with the inverse image
of the original nonzero open, giving the actual base-change isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The unit of a pulled-back group projects to the original unit. -/
theorem coefficientPullback_unit_fst (X : Over (Spec (.of R))) [GrpObj X] :
    (η[(coefficientPullbackFunctor (R := R) S).obj X]).left ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (η[X]).left := by
  rw [CategoryTheory.Functor.obj.η_def, Over.comp_left, Category.assoc]
  change (Functor.LaxMonoidal.ε
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))).left ≫
      pullback.lift
        (pullback.fst (𝟙 (Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ (η[X]).left)
        (pullback.snd (𝟙 (Spec (.of R)))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Over.ε_pullback_left]
  have h : pullback.fst (𝟙 (Spec (.of R)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.snd (𝟙 (Spec (.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    simpa using (pullback.condition (f := 𝟙 (Spec (.of R)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [h]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

variable [IsNoetherianRing R] [IsDomain R]
variable [IsNoetherianRing S] [IsDomain S] [W.IsElliptic]
variable (n : ℕ)

/-- The coefficient-extension map on the underlying torsion schemes. -/
def coefficientTorsionMorphism :
    (torsionModel (W.map (algebraMap R S)) n).left ⟶ (torsionModel W n).left :=
  (coefficientTorsionIso W S n).hom.left ≫
    pullback.fst (torsionModel W n).hom (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The torsion coefficient map lies over the map of coefficient bases. -/
theorem coefficientTorsionMorphism_toBase :
    coefficientTorsionMorphism W S n ≫ (torsionModel W n).hom =
      (torsionModel (W.map (algebraMap R S)) n).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  dsimp only [coefficientTorsionMorphism]
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (coefficientTorsionIso W S n).hom.w

/-- Coefficient extension preserves the zero section of torsion. -/
theorem torsionZeroSection_coefficient :
    torsionZeroSection (W.map (algebraMap R S)) n ≫ coefficientTorsionMorphism W S n =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ torsionZeroSection W n := by
  dsimp only [coefficientTorsionMorphism, torsionZeroSection]
  rw [← Category.assoc]
  have h := congrArg Over.Hom.left (IsMonHom.one_hom (coefficientTorsionIso W S n).hom)
  change _ ≫ (coefficientTorsionIso W S n).hom.left = _ at h
  rw [h]
  exact coefficientPullback_unit_fst S (torsionModel W n)

/-- The represented torsion square is cartesian. -/
theorem coefficientTorsion_isPullback :
    IsPullback (coefficientTorsionMorphism W S n)
      (torsionModel (W.map (algebraMap R S)) n).hom (torsionModel W n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  IsPullback.of_iso_pullback ⟨coefficientTorsionMorphism_toBase W S n⟩
    ((Over.forget _).mapIso (coefficientTorsionIso W S n)) rfl
    (coefficientTorsionIso W S n).hom.w

/-- The square of zero sections is cartesian. -/
theorem torsionZeroSection_coefficient_isPullback :
    IsPullback (torsionZeroSection (W.map (algebraMap R S)) n)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (coefficientTorsionMorphism W S n) (torsionZeroSection W n) := by
  have h : IsPullback
      (torsionZeroSection (W.map (algebraMap R S)) n ≫
        (torsionModel (W.map (algebraMap R S)) n).hom)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (torsionZeroSection W n ≫ (torsionModel W n).hom) := by
    rw [torsionZeroSection_toBase, torsionZeroSection_toBase]
    exact IsPullback.of_id_fst
  exact h.of_right (torsionZeroSection_coefficient W S n)
    (coefficientTorsion_isPullback W S n).flip

private theorem scheme_pullback_range {P X Y Z : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) :
    Set.range a = f ⁻¹' Set.range g := by
  have he : a = h.isoPullback.hom ≫ pullback.fst f g := h.isoPullback_hom_fst.symm
  rw [he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [(h.isoPullback.hom).surjective.range_eq, Set.image_univ]
  exact Scheme.Pullback.range_fst f g

/-- The complement of zero is preserved by inverse image. -/
theorem nonzeroTorsionOpen_coefficient [NeZero n] :
    nonzeroTorsionOpen (W.map (algebraMap R S)) n =
      (coefficientTorsionMorphism W S n) ⁻¹ᵁ nonzeroTorsionOpen W n := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (torsionZeroSection (W.map (algebraMap R S)) n))ᶜ =
    (coefficientTorsionMorphism W S n) ⁻¹'
      (Set.range (torsionZeroSection W n))ᶜ
  rw [scheme_pullback_range (torsionZeroSection_coefficient_isPullback W S n)]
  rfl

variable [NeZero n]

/-- The coefficient map restricted to nonzero torsion. -/
def coefficientNonzeroTorsionMorphism :
    (nonzeroTorsionModel (W.map (algebraMap R S)) n).left ⟶
      (nonzeroTorsionModel W n).left :=
  (coefficientTorsionMorphism W S n).resLE
    (nonzeroTorsionOpen W n) (nonzeroTorsionOpen (W.map (algebraMap R S)) n)
    (nonzeroTorsionOpen_coefficient W S n).le

/-- The restricted map agrees with the full torsion coefficient map. -/
@[reassoc (attr := simp)] theorem coefficientNonzeroTorsionMorphism_inclusion :
    coefficientNonzeroTorsionMorphism W S n ≫ (nonzeroTorsionInclusion W n).left =
      (nonzeroTorsionInclusion (W.map (algebraMap R S)) n).left ≫
        coefficientTorsionMorphism W S n :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The nonzero torsion square is cartesian. -/
theorem coefficientNonzeroTorsion_isPullback :
    IsPullback (coefficientNonzeroTorsionMorphism W S n)
      (nonzeroTorsionModel (W.map (algebraMap R S)) n).hom
      (nonzeroTorsionModel W n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have h : IsPullback (coefficientNonzeroTorsionMorphism W S n)
      (nonzeroTorsionOpen (W.map (algebraMap R S)) n).ι
      (nonzeroTorsionOpen W n).ι (coefficientTorsionMorphism W S n) := by
    apply IsOpenImmersion.isPullback
    · exact (coefficientNonzeroTorsionMorphism_inclusion W S n).symm
    · simpa only [Scheme.Opens.opensRange_ι] using
        (nonzeroTorsionOpen_coefficient W S n).symm
  exact h.paste_vert (coefficientTorsion_isPullback W S n)

/-- Nonzero torsion commutes with coefficient extension. -/
def coefficientNonzeroTorsionIso :
    nonzeroTorsionModel (W.map (algebraMap R S)) n ≅
      (coefficientPullbackFunctor (R := R) S).obj (nonzeroTorsionModel W n) :=
  Over.isoMk (coefficientNonzeroTorsion_isPullback W S n).isoPullback
    (coefficientNonzeroTorsion_isPullback W S n).isoPullback_hom_snd

/-- The base-change isomorphism projects to the restricted coefficient map. -/
@[reassoc (attr := simp)] theorem coefficientNonzeroTorsionIso_hom_fst :
    (coefficientNonzeroTorsionIso W S n).hom.left ≫
        pullback.fst (nonzeroTorsionModel W n).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      coefficientNonzeroTorsionMorphism W S n :=
  (coefficientNonzeroTorsion_isPullback W S n).isoPullback_hom_fst

end WeierstrassCurve.CubicCharts
