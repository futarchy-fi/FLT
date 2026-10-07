/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicIncidencePoints

/-! # The represented cyclic family as a finite étale commutative group

The incidence subscheme represents a subgroup of the actual torsion point
functor over the parameter base. Closure under multiplication and inverse
follows from its geometric fibers and the already constructed open embedding.
Representability supplies the relative group law with all its axioms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonObj
open MonoidalCategory CartesianMonoidalCategory Opposite
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u

/-- Algebraically closed field-valued points cover every point over an affine base. -/
theorem over_geometricPoints_cover {R : Type u} [CommRing R]
    (X : Over (Spec (.of R))) (U : Set X.left)
    (h : ∀ (K : Type u) [Field K] [Algebra R K] [IsAlgClosed K]
      (x : pointSource (R := R) K ⟶ X), Set.range x.left ⊆ U) :
    ∀ x, x ∈ U := by
  intro x
  let k := X.left.residueField x
  let K := AlgebraicClosure k
  let f : Spec (.of K) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ X.left.fromSpecResidueField x
  let φ : R →+* K := (Spec.preimage (f ≫ X.hom)).hom
  let : Algebra R K := φ.toAlgebra
  let g : pointSource K ⟶ X := Over.homMk f (by
    change f ≫ X.hom = Spec.map (CommRingCat.ofHom φ)
    exact (Spec.map_preimage _).symm)
  have hx := h K g (Set.mem_range_self (IsLocalRing.closedPoint K))
  change (X.left.fromSpecResidueField x) _ ∈ U at hx
  rwa [Scheme.fromSpecResidueField_apply] at hx

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]

/-- The actual incidence family as a scheme over its cyclic parameters. -/
abbrev cyclicFamilyModel : Over (scalarQuotientModel W p).left :=
  Over.mk (cyclicIncidenceToBase W p)

/-- A parameter-scheme object regarded over the original coefficient base. -/
abbrev cyclicCoefficientSource (X : Over (scalarQuotientModel W p).left) :
    Over (Spec (.of R)) := Over.mk (X.hom ≫ (scalarQuotientModel W p).hom)

/-- A point of the cyclic family determines an actual torsion point. -/
def cyclicPointToTorsion (X : Over (scalarQuotientModel W p).left)
    (f : X ⟶ cyclicFamilyModel W p) :
    cyclicCoefficientSource W p X ⟶ torsionModel W p :=
  Over.homMk (f.left ≫ cyclicIncidenceInclusion W p ≫ pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition,
      ← Category.assoc (cyclicIncidenceInclusion W p),
      cyclicIncidenceInclusion_toBase, ← Category.assoc]
    exact congrArg (fun h => h ≫ (scalarQuotientModel W p).hom) f.w)

/-- The cyclic-family point map into torsion is injective for every scheme source. -/
theorem cyclicPointToTorsion_injective (X : Over (scalarQuotientModel W p).left) :
    Function.Injective (cyclicPointToTorsion W p X) := by
  have := cyclicIncidenceInclusion_open W p
  intro a b h
  apply Over.OverMorphism.ext
  apply (cancel_mono (cyclicIncidenceInclusion W p)).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, cyclicIncidenceInclusion_toBase]
    exact a.w.trans b.w.symm
  · exact congrArg Over.Hom.left h

/-- The cyclic parameter underlying a geometric point of a source scheme. -/
def cyclicParameterPoint (X : Over (scalarQuotientModel W p).left)
    (K : Type u) [Field K] [Algebra R K]
    (x : pointSource K ⟶ cyclicCoefficientSource W p X) :
    pointSource K ⟶ scalarQuotientModel W p :=
  Over.homMk (x.left ≫ X.hom) (by rw [Category.assoc]; exact x.w)

/-- Every geometric specialization of a family point lies in the classified subgroup. -/
theorem cyclicPointToTorsion_mem (X : Over (scalarQuotientModel W p).left)
    (f : X ⟶ cyclicFamilyModel W p)
    (K : Type u) [Field K] [Algebra R K] [IsAlgClosed K] [DecidableEq K]
    (x : pointSource K ⟶ cyclicCoefficientSource W p X) :
    (classicalTorsionMulEquiv W K p (x ≫ cyclicPointToTorsion W p X f)).toAdd.val ∈
      (scalarQuotientPrimeSubgroupEquiv W p K (cyclicParameterPoint W p X K x)).val := by
  let z : {z : Spec (.of K) ⟶ cyclicIncidenceFamily W p //
      z ≫ cyclicIncidenceToBase W p = (cyclicParameterPoint W p X K x).left} :=
    ⟨x.left ≫ f.left, by
      rw [Category.assoc]
      exact congrArg (fun h => x.left ≫ h) f.w⟩
  have hz := cyclicIncidenceClassicalPoint_mem W p K (cyclicParameterPoint W p X K x) z
  have he : cyclicIncidenceTorsionPoint W p K (cyclicParameterPoint W p X K x) z =
      x ≫ cyclicPointToTorsion W p X f := by
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _
  simpa only [cyclicIncidenceClassicalPoint, he] using hz

/-- A torsion point lying in the classified subgroups lifts to the incidence family. -/
theorem cyclicPoint_lift_of_geometric (X : Over (scalarQuotientModel W p).left)
    (b : cyclicCoefficientSource W p X ⟶ torsionModel W p)
    (hb : ∀ (K : Type u) [Field K] [Algebra R K] [IsAlgClosed K] [DecidableEq K]
      (x : pointSource K ⟶ cyclicCoefficientSource W p X),
      (classicalTorsionMulEquiv W K p (x ≫ b)).toAdd.val ∈
        (scalarQuotientPrimeSubgroupEquiv W p K (cyclicParameterPoint W p X K x)).val) :
    ∃ f : X ⟶ cyclicFamilyModel W p, cyclicPointToTorsion W p X f = b := by
  classical
  let pair : X.left ⟶ cyclicIncidenceAmbient W p :=
    pullback.lift X.hom b.left b.w.symm
  have hr : Set.range pair ⊆ Set.range (cyclicIncidenceInclusion W p) := by
    rintro _ ⟨t, rfl⟩
    apply over_geometricPoints_cover (cyclicCoefficientSource W p X)
      {t | pair t ∈ Set.range (cyclicIncidenceInclusion W p)} ?_ t
    intro K _ _ _ x
    let q := cyclicParameterPoint W p X K x
    let e := cyclicIncidenceSubgroupEquiv W p K q
    obtain ⟨z, hz⟩ := e.surjective
      ⟨(classicalTorsionMulEquiv W K p (x ≫ b)).toAdd.val, hb K x⟩
    have he : cyclicIncidenceTorsionPoint W p K q z = x ≫ b := by
      apply (classicalTorsionMulEquiv W K p).injective
      exact Subtype.ext (congrArg (fun z : (scalarQuotientPrimeSubgroupEquiv W p K q).val =>
        z.val) hz)
    have hf : z.val ≫ cyclicIncidenceInclusion W p = x.left ≫ pair := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, cyclicIncidenceInclusion_toBase,
          pair, pullback.lift_fst, q, cyclicParameterPoint, Over.homMk_left] using z.property
      · exact (congrArg Over.Hom.left he).trans
          (by simp only [pair, Category.assoc, pullback.lift_snd]; rfl)
    rintro _ ⟨s, rfl⟩
    exact ⟨z.val s, congrArg (fun f : Spec (.of K) ⟶ cyclicIncidenceAmbient W p => f s) hf⟩
  have := cyclicIncidenceInclusion_open W p
  let f := IsOpenImmersion.lift (cyclicIncidenceInclusion W p) pair hr
  have hf : f ≫ cyclicIncidenceInclusion W p = pair := IsOpenImmersion.lift_fac _ _ _
  let f' : X ⟶ cyclicFamilyModel W p := Over.homMk f (by
    change f ≫ cyclicIncidenceToBase W p = X.hom
    rw [← cyclicIncidenceInclusion_toBase, ← Category.assoc, hf]
    exact pullback.lift_fst _ _ _)
  refine ⟨f', ?_⟩
  apply Over.OverMorphism.ext
  change f ≫ cyclicIncidenceInclusion W p ≫ pullback.snd _ _ = b.left
  rw [← Category.assoc, hf]
  exact pullback.lift_snd _ _ _

/-- The represented cyclic subgroup inside torsion points over an arbitrary source. -/
def cyclicPointGroup (X : Over (scalarQuotientModel W p).left) :
    Subgroup (cyclicCoefficientSource W p X ⟶ torsionModel W p) where
  carrier := Set.range (cyclicPointToTorsion W p X)
  one_mem' := by
    apply cyclicPoint_lift_of_geometric
    intro K _ _ _ _ x
    simp only [MonObj.comp_one, map_one]
    exact AddSubgroup.zero_mem _
  mul_mem' := by
    rintro a b ⟨f, rfl⟩ ⟨g, rfl⟩
    apply cyclicPoint_lift_of_geometric
    intro K _ _ _ _ x
    rw [MonObj.comp_mul, map_mul]
    exact AddSubgroup.add_mem _
      (cyclicPointToTorsion_mem W p X f K x) (cyclicPointToTorsion_mem W p X g K x)
  inv_mem' := by
    rintro a ⟨f, rfl⟩
    apply cyclicPoint_lift_of_geometric
    intro K _ _ _ _ x
    rw [GrpObj.comp_inv, map_inv]
    exact AddSubgroup.neg_mem _ (cyclicPointToTorsion_mem W p X f K x)

/-- A map over cyclic parameters also gives a map over the coefficient base. -/
def cyclicCoefficientMap {X Y : Over (scalarQuotientModel W p).left} (f : X ⟶ Y) :
    cyclicCoefficientSource W p X ⟶ cyclicCoefficientSource W p Y :=
  Over.homMk f.left (by
    change f.left ≫ (Y.hom ≫ (scalarQuotientModel W p).hom) = _
    rw [← Category.assoc, f.w]
    rfl)

omit [Fact p.Prime] in
/-- The incidence map commutes with restriction along every source morphism. -/
theorem cyclicPointToTorsion_naturality {X Y : Over (scalarQuotientModel W p).left}
    (f : X ⟶ Y) (g : Y ⟶ cyclicFamilyModel W p) :
    cyclicCoefficientMap W p f ≫ cyclicPointToTorsion W p Y g =
      cyclicPointToTorsion W p X (f ≫ g) := by
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm

/-- Restriction of cyclic-family points is a group homomorphism. -/
def cyclicPointRestriction {X Y : Over (scalarQuotientModel W p).left} (f : X ⟶ Y) :
    cyclicPointGroup W p Y →* cyclicPointGroup W p X where
  toFun b := ⟨cyclicCoefficientMap W p f ≫ b.val, by
    obtain ⟨g, hg⟩ := b.property
    exact ⟨f ≫ g, (cyclicPointToTorsion_naturality W p f g).symm.trans
      (congrArg (fun h => cyclicCoefficientMap W p f ≫ h) hg)⟩⟩
  map_one' := Subtype.ext (MonObj.comp_one _)
  map_mul' a b := Subtype.ext (MonObj.comp_mul _ _ _)

/-- The cyclic-family point functor takes values in commutative groups. -/
def cyclicPointFunctor : (Over (scalarQuotientModel W p).left)ᵒᵖ ⥤ CommGrpCat where
  obj X := CommGrpCat.of (cyclicPointGroup W p X.unop)
  map f := CommGrpCat.ofHom (cyclicPointRestriction W p f.unop)
  map_id X := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro b
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro b
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _

/-- The incidence family represents the actual cyclic subgroup of torsion points. -/
def cyclicPointEquiv (X : Over (scalarQuotientModel W p).left) :
    (X ⟶ cyclicFamilyModel W p) ≃ cyclicPointGroup W p X :=
  Equiv.ofBijective (fun f => ⟨cyclicPointToTorsion W p X f, ⟨f, rfl⟩⟩)
    ⟨fun _ _ h => cyclicPointToTorsion_injective W p X (congrArg Subtype.val h), by
      rintro ⟨b, f, hf⟩
      exact ⟨f, Subtype.ext hf⟩⟩

/-- Representability of the cyclic subgroup functor, including its naturality. -/
def cyclicPointRepresentable :
    (cyclicPointFunctor W p ⋙ forget _).RepresentableBy (cyclicFamilyModel W p) where
  homEquiv {X} := cyclicPointEquiv W p X
  homEquiv_comp f g := by
    apply Subtype.ext
    exact (cyclicPointToTorsion_naturality W p f g).symm

/-- The actual cyclic incidence family is a commutative group over its parameter scheme. -/
instance cyclicFamilyCommGrpObj : CommGrpObj (cyclicFamilyModel W p) :=
  CommGrpObj.ofRepresentableBy (cyclicFamilyModel W p)
    (cyclicPointFunctor W p) (cyclicPointRepresentable W p)

/-- The representing equivalence respects the relative group law. -/
def cyclicPointMulEquiv (X : Over (scalarQuotientModel W p).left) :
    (X ⟶ cyclicFamilyModel W p) ≃* cyclicPointGroup W p X where
  toEquiv := cyclicPointEquiv W p X
  map_mul' f g :=
    ((yonedaGrpObjIsoOfRepresentableBy (cyclicFamilyModel W p)
      (cyclicPointFunctor W p ⋙ forget₂ CommGrpCat GrpCat)
      (cyclicPointRepresentable W p)).hom.app (op X)).hom.map_mul f g

/-- The relative group law is the restriction of the actual torsion group law. -/
theorem cyclicPointToTorsion_mul (X : Over (scalarQuotientModel W p).left)
    (f g : X ⟶ cyclicFamilyModel W p) :
    cyclicPointToTorsion W p X (f * g) =
      cyclicPointToTorsion W p X f * cyclicPointToTorsion W p X g :=
  congrArg Subtype.val ((cyclicPointMulEquiv W p X).map_mul f g)

/-- The identity of the cyclic family is the identity torsion point. -/
theorem cyclicPointToTorsion_one (X : Over (scalarQuotientModel W p).left) :
    cyclicPointToTorsion W p X 1 = 1 :=
  congrArg Subtype.val (cyclicPointMulEquiv W p X).map_one

/-- Every point of the cyclic family is killed by the prime level. -/
theorem cyclicFamilyPoint_pow_eq_one {X : Over (scalarQuotientModel W p).left}
    (f : X ⟶ cyclicFamilyModel W p) : f ^ p = 1 := by
  apply (cyclicPointMulEquiv W p X).injective
  rw [map_pow, map_one]
  exact Subtype.ext (torsionPoint_pow_eq_one W p _)

/-- The represented cyclic group is finite over its parameter scheme. -/
instance cyclicFamilyFinite : IsFinite (cyclicFamilyModel W p).hom :=
  cyclicIncidenceToBase_finite W p

/-- The represented cyclic group is étale over its parameter scheme. -/
instance cyclicFamilyEtale : Etale (cyclicFamilyModel W p).hom :=
  cyclicIncidenceToBase_etale W p

end WeierstrassCurve.CubicCharts
