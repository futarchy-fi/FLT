/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeScalars
public import FLT.EllipticCurve.CubicScalarDescent
/-! # Base change of prime cyclic-subgroup parameters

Scalar descent gives the coefficient map on the actual invariant quotient.
The comparison with its pullback is étale and surjective; classification
of geometric generator fibers makes it injective on geometric points.
Consequently it is an isomorphism, without requiring p-1 to be invertible.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u

private theorem over_etale_iso_of_geometric_injective
    {A : Type u} [CommRing A] {X Y : Over (Spec (.of A))} (f : X ⟶ Y)
    [Etale f.left] [Surjective f.left]
    (hi : ∀ (K : Type u) [Field K] [Algebra A K] [IsAlgClosed K],
      Function.Injective (fun x : pointSource (R := A) K ⟶ X => x ≫ f)) :
    IsIso f.left := by
  let D : Over (Spec (.of A)) := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  have hd : Surjective (pullback.diagonal f.left) := by
    constructor
    apply over_geometricPoints_cover D (Set.range (pullback.diagonal f.left))
    intro K _ _ _ t z hz
    obtain ⟨y, rfl⟩ := hz
    let a : pointSource (R := A) K ⟶ X :=
      Over.homMk (t.left ≫ pullback.fst f.left f.left) (by
        rw [Category.assoc]
        exact t.w)
    let b : pointSource (R := A) K ⟶ X :=
      Over.homMk (t.left ≫ pullback.snd f.left f.left) (by
        rw [← f.w, Category.assoc,
          ← Category.assoc (pullback.snd f.left f.left) f.left Y.hom,
          ← pullback.condition, Category.assoc, f.w]
        exact t.w)
    have hab : a = b := hi K (by
      apply Over.OverMorphism.ext
      change (t.left ≫ pullback.fst _ _) ≫ f.left =
        (t.left ≫ pullback.snd _ _) ≫ f.left
      rw [Category.assoc, Category.assoc, pullback.condition])
    have ht : t.left = a.left ≫ pullback.diagonal f.left := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        rfl
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact (congrArg Over.Hom.left hab).symm
    exact ⟨a.left y, congrArg (fun g : Spec (.of K) ⟶ D.left => g y) ht.symm⟩
  have : IsIso (pullback.diagonal f.left) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hd⟩
  have : Mono f.left := (pullback.isIso_diagonal_iff f.left).mp inferInstance
  have : IsOpenImmersion f.left := IsOpenImmersion.of_flat_of_mono f.left
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsDomain R]
variable [IsNoetherianRing S] [IsDomain S] [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))]

omit [Fact (IsUnit (p : S))] in
/-- The coefficient map followed by the quotient is invariant on generators. -/
theorem coefficientScalarGenerators_invariant (a : (ZMod p)ˣ) :
    (nonzeroTorsionScalarAction (W.map (algebraMap R S)) p a).hom.left ≫
        coefficientNonzeroTorsionMorphism W S p ≫ (scalarQuotientMap W p).left =
      coefficientNonzeroTorsionMorphism W S p ≫ (scalarQuotientMap W p).left := by
  rw [← Category.assoc, coefficientNonzeroTorsionMorphism_scalar, Category.assoc]
  exact congrArg (fun f => coefficientNonzeroTorsionMorphism W S p ≫ f)
    (congrArg Over.Hom.left (scalarQuotientMap_invariant W p a))

/-- The coefficient map descended to cyclic-subgroup parameters. -/
def coefficientScalarQuotientMorphism :
    (scalarQuotientModel (W.map (algebraMap R S)) p).left ⟶
      (scalarQuotientModel W p).left :=
  scalarQuotientDesc (W.map (algebraMap R S)) p
    (coefficientNonzeroTorsionMorphism W S p ≫ (scalarQuotientMap W p).left)
    (coefficientScalarGenerators_invariant W S p)

/-- Descent recovers the coefficient map on generators. -/
@[reassoc (attr := simp)] theorem coefficientScalarQuotientMorphism_generators :
    (scalarQuotientMap (W.map (algebraMap R S)) p).left ≫
        coefficientScalarQuotientMorphism W S p =
      coefficientNonzeroTorsionMorphism W S p ≫ (scalarQuotientMap W p).left :=
  scalarQuotientDesc_fac _ _ _ _

omit [Fact (IsUnit (p : R))] [Fact (IsUnit (p : S))] in
/-- The restricted coefficient map lies over coefficient extension. -/
theorem coefficientNonzeroTorsionMorphism_toBase :
    coefficientNonzeroTorsionMorphism W S p ≫ (nonzeroTorsionModel W p).hom =
      (nonzeroTorsionModel (W.map (algebraMap R S)) p).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  (coefficientNonzeroTorsion_isPullback W S p).w

/-- The descended coefficient map lies over coefficient extension. -/
theorem coefficientScalarQuotientMorphism_toBase :
    coefficientScalarQuotientMorphism W S p ≫ (scalarQuotientModel W p).hom =
      (scalarQuotientModel (W.map (algebraMap R S)) p).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (scalarQuotientMap (W.map (algebraMap R S)) p).left).mp
  rw [← Category.assoc, coefficientScalarQuotientMorphism_generators,
    Category.assoc, (scalarQuotientMap W p).w, coefficientNonzeroTorsionMorphism_toBase,
    ← Category.assoc, (scalarQuotientMap (W.map (algebraMap R S)) p).w]

/-- Comparison with the base change of the original cyclic parameter scheme. -/
def coefficientScalarQuotientComparison :
    scalarQuotientModel (W.map (algebraMap R S)) p ⟶
      (coefficientPullbackFunctor (R := R) S).obj (scalarQuotientModel W p) :=
  Over.homMk (pullback.lift (coefficientScalarQuotientMorphism W S p)
    (scalarQuotientModel (W.map (algebraMap R S)) p).hom
    (coefficientScalarQuotientMorphism_toBase W S p)) (pullback.lift_snd _ _ _)

/-- The comparison projects to the descended coefficient map. -/
@[reassoc (attr := simp)] theorem coefficientScalarQuotientComparison_fst :
    (coefficientScalarQuotientComparison W S p).left ≫
        pullback.fst (scalarQuotientModel W p).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      coefficientScalarQuotientMorphism W S p :=
  pullback.lift_fst _ _ _

/-- The comparison agrees with base change on generators. -/
theorem coefficientScalarQuotientComparison_generators :
    scalarQuotientMap (W.map (algebraMap R S)) p ≫
        coefficientScalarQuotientComparison W S p =
      (coefficientNonzeroTorsionIso W S p).hom ≫
        (coefficientPullbackFunctor (R := R) S).map (scalarQuotientMap W p) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, coefficientScalarQuotientComparison_fst,
      coefficientScalarQuotientMorphism_generators, coefficientPullback_map_fst]
    rw [← Category.assoc, coefficientNonzeroTorsionIso_hom_fst]
  · exact (scalarQuotientMap (W.map (algebraMap R S)) p ≫
      coefficientScalarQuotientComparison W S p).w.trans
        ((coefficientNonzeroTorsionIso W S p).hom ≫
          (coefficientPullbackFunctor (R := R) S).map (scalarQuotientMap W p)).w.symm

/-- The comparison is étale. -/
instance coefficientScalarQuotientComparisonEtale :
    Etale (coefficientScalarQuotientComparison W S p).left := by
  have := scalarQuotientModel_etale (W.map (algebraMap R S)) p
  have h : Etale ((coefficientScalarQuotientComparison W S p).left ≫
      ((coefficientPullbackFunctor (R := R) S).obj (scalarQuotientModel W p)).hom) := by
    rw [(coefficientScalarQuotientComparison W S p).w]
    infer_instance
  have := scalarQuotientModel_etale W p
  have : Etale ((coefficientPullbackFunctor (R := R) S).obj
      (scalarQuotientModel W p)).hom :=
    inferInstanceAs (Etale (pullback.snd (scalarQuotientModel W p).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))))
  exact Etale.of_comp (coefficientScalarQuotientComparison W S p).left
    ((coefficientPullbackFunctor (R := R) S).obj (scalarQuotientModel W p)).hom

/-- Every base-changed cyclic parameter is in the image of the comparison. -/
instance coefficientScalarQuotientComparisonSurjective :
    Surjective (coefficientScalarQuotientComparison W S p).left := by
  have hq : Surjective
      ((coefficientPullbackFunctor (R := R) S).map (scalarQuotientMap W p)).left :=
    MorphismProperty.overPullbackMap (P := @Surjective)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (scalarQuotientMap W p)
      (scalarQuotientMap_surjective W p)
  have : Surjective ((scalarQuotientMap (W.map (algebraMap R S)) p).left ≫
      (coefficientScalarQuotientComparison W S p).left) := by
    rw [← Over.comp_left, coefficientScalarQuotientComparison_generators, Over.comp_left]
    infer_instance
  exact Surjective.of_comp (scalarQuotientMap (W.map (algebraMap R S)) p).left _

variable (K : Type u) [Field K] [IsAlgClosed K] [Algebra S K] [Algebra R K]
variable [IsScalarTower R S K]

/-- A generator over the new base defines a generator over the original base. -/
def coefficientNonzeroTorsionFieldPoint
    (x : pointSource (R := S) K ⟶ nonzeroTorsionModel (W.map (algebraMap R S)) p) :
    pointSource (R := R) K ⟶ nonzeroTorsionModel W p :=
  Over.homMk (x.left ≫ coefficientNonzeroTorsionMorphism W S p) (by
    rw [Category.assoc, coefficientNonzeroTorsionMorphism_toBase, ← Category.assoc, x.w]
    exact coefficient_base_comp (R := R) (K := K) S)

/-- The comparison is injective on geometric points. -/
theorem coefficientScalarQuotientComparison_field_injective :
    Function.Injective (fun x : pointSource (R := S) K ⟶
      scalarQuotientModel (W.map (algebraMap R S)) p =>
        x ≫ coefficientScalarQuotientComparison W S p) := by
  intro x y h
  obtain ⟨a, rfl⟩ := scalarQuotientFieldPoint_surjective (W.map (algebraMap R S)) p K x
  obtain ⟨b, rfl⟩ := scalarQuotientFieldPoint_surjective (W.map (algebraMap R S)) p K y
  have hc : coefficientNonzeroTorsionFieldPoint W S p K a ≫ scalarQuotientMap W p =
      coefficientNonzeroTorsionFieldPoint W S p K b ≫ scalarQuotientMap W p := by
    apply Over.OverMorphism.ext
    have ht := congrArg (fun f => f.left ≫
      pullback.fst (scalarQuotientModel W p).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) h
    simpa only [Over.comp_left, Category.assoc, coefficientScalarQuotientComparison_fst,
      coefficientScalarQuotientMorphism_generators, coefficientNonzeroTorsionFieldPoint,
      Over.homMk_left] using ht
  obtain ⟨c, hc⟩ := (scalarQuotientFieldPoint_fiber_hom W p K
    (coefficientNonzeroTorsionFieldPoint W S p K a)
    (coefficientNonzeroTorsionFieldPoint W S p K b)).mp hc
  have hab : a = b ≫ (nonzeroTorsionScalarAction (W.map (algebraMap R S)) p c).hom := by
    apply Over.OverMorphism.ext
    apply (coefficientNonzeroTorsion_isPullback W S p).hom_ext
    · have ht := congrArg Over.Hom.left hc
      change a.left ≫ coefficientNonzeroTorsionMorphism W S p =
        (b.left ≫ coefficientNonzeroTorsionMorphism W S p) ≫
          (nonzeroTorsionScalarAction W p c).hom.left at ht
      simp only [Over.comp_left, Category.assoc, coefficientNonzeroTorsionMorphism_scalar]
      simpa only [Category.assoc] using ht
    · exact a.w.trans
        (b ≫ (nonzeroTorsionScalarAction (W.map (algebraMap R S)) p c).hom).w.symm
  change a ≫ scalarQuotientMap (W.map (algebraMap R S)) p =
    b ≫ scalarQuotientMap (W.map (algebraMap R S)) p
  rw [hab, Category.assoc, scalarQuotientMap_invariant]

/-- The comparison is an isomorphism of schemes over the new base. -/
instance coefficientScalarQuotientComparisonIsIso :
    IsIso (coefficientScalarQuotientComparison W S p) := by
  have hl : IsIso (coefficientScalarQuotientComparison W S p).left := by
    apply over_etale_iso_of_geometric_injective
    intro L _ _ _
    let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
    let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
    exact coefficientScalarQuotientComparison_field_injective W S p L
  have : IsIso ((Over.forget (Spec (.of S))).map
      (coefficientScalarQuotientComparison W S p)) := hl
  exact isIso_of_reflects_iso (coefficientScalarQuotientComparison W S p)
    (Over.forget (Spec (.of S)))

/-- Prime cyclic-subgroup parameters commute with coefficient extension. -/
def coefficientScalarQuotientIso :
    scalarQuotientModel (W.map (algebraMap R S)) p ≅
      (coefficientPullbackFunctor (R := R) S).obj (scalarQuotientModel W p) :=
  asIso (coefficientScalarQuotientComparison W S p)

/-- The square of prime cyclic-parameter schemes is cartesian. -/
theorem coefficientScalarQuotient_isPullback :
    IsPullback (coefficientScalarQuotientMorphism W S p)
      (scalarQuotientModel (W.map (algebraMap R S)) p).hom
      (scalarQuotientModel W p).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  IsPullback.of_iso_pullback ⟨coefficientScalarQuotientMorphism_toBase W S p⟩
    ((Over.forget _).mapIso (coefficientScalarQuotientIso W S p))
    (coefficientScalarQuotientComparison_fst W S p)
    (coefficientScalarQuotientComparison W S p).w

end WeierstrassCurve.CubicCharts
