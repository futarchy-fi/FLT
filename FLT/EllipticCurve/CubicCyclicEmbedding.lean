/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicGroup

/-! # The cyclic family is a closed subgroup of the base-changed torsion

The torsion pullback represents the original torsion points over sources
mapping to the parameter scheme. Its represented group law makes the
incidence embedding a closed immersion and a group homomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonObj
open MonoidalCategory CartesianMonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]

/-- The actual torsion scheme after base change to the cyclic parameter space. -/
abbrev cyclicAmbientGroup : Over (scalarQuotientModel W p).left :=
  Over.mk (pullback.snd (torsionModel W p).hom (scalarQuotientModel W p).hom)

/-- Points of the torsion pullback are torsion points over the coefficient base. -/
def cyclicAmbientPointEquiv (X : Over (scalarQuotientModel W p).left) :
    (X ⟶ cyclicAmbientGroup W p) ≃
      (cyclicCoefficientSource W p X ⟶ torsionModel W p) where
  toFun f := Over.homMk (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun h => h ≫ (scalarQuotientModel W p).hom) f.w)
  invFun f := Over.homMk (pullback.lift f.left X.hom f.w) (pullback.lift_snd _ _ _)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using f.w.symm
  right_inv f := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- The pullback torsion point functor is commutative-group-valued. -/
def cyclicAmbientPointFunctor :
    (Over (scalarQuotientModel W p).left)ᵒᵖ ⥤ CommGrpCat where
  obj X := CommGrpCat.of (cyclicCoefficientSource W p X.unop ⟶ torsionModel W p)
  map f := CommGrpCat.ofHom {
    toFun b := cyclicCoefficientMap W p f.unop ≫ b
    map_one' := MonObj.comp_one _
    map_mul' a b := MonObj.comp_mul _ _ _ }
  map_id X := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro b
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro b
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _

/-- The torsion pullback represents the commutative torsion point functor. -/
def cyclicAmbientPointRepresentable :
    (cyclicAmbientPointFunctor W p ⋙ forget _).RepresentableBy (cyclicAmbientGroup W p) where
  homEquiv {X} := cyclicAmbientPointEquiv W p X
  homEquiv_comp f g := by
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _

/-- The group structure on the base-changed torsion scheme. -/
instance cyclicAmbientCommGrpObj : CommGrpObj (cyclicAmbientGroup W p) :=
  CommGrpObj.ofRepresentableBy (cyclicAmbientGroup W p)
    (cyclicAmbientPointFunctor W p) (cyclicAmbientPointRepresentable W p)

/-- The pullback point equivalence respects the torsion group law. -/
def cyclicAmbientPointMulEquiv (X : Over (scalarQuotientModel W p).left) :
    (X ⟶ cyclicAmbientGroup W p) ≃*
      (cyclicCoefficientSource W p X ⟶ torsionModel W p) where
  toEquiv := cyclicAmbientPointEquiv W p X
  map_mul' f g :=
    ((yonedaGrpObjIsoOfRepresentableBy (cyclicAmbientGroup W p)
      (cyclicAmbientPointFunctor W p ⋙ forget₂ CommGrpCat GrpCat)
      (cyclicAmbientPointRepresentable W p)).hom.app (Opposite.op X)).hom.map_mul f g

/-- The incidence family maps into the actual base-changed torsion scheme. -/
def cyclicFamilyInclusion : cyclicFamilyModel W p ⟶ cyclicAmbientGroup W p :=
  (cyclicAmbientPointEquiv W p (cyclicFamilyModel W p)).symm
    (cyclicPointToTorsion W p (cyclicFamilyModel W p) (𝟙 _))

omit [Fact p.Prime] in
/-- The subgroup inclusion induces the previously constructed torsion point map. -/
theorem cyclicFamilyInclusion_point (X : Over (scalarQuotientModel W p).left)
    (f : X ⟶ cyclicFamilyModel W p) :
    cyclicAmbientPointEquiv W p X (f ≫ cyclicFamilyInclusion W p) =
      cyclicPointToTorsion W p X f := by
  apply Over.OverMorphism.ext
  change (f.left ≫ _) ≫ pullback.fst _ _ = _
  simp [cyclicFamilyInclusion, cyclicAmbientPointEquiv, cyclicPointToTorsion]

/-- The subgroup inclusion on arbitrary scheme-valued points is a homomorphism. -/
def cyclicFamilyPointInclusionHom (X : Over (scalarQuotientModel W p).left) :
    (X ⟶ cyclicFamilyModel W p) →* (X ⟶ cyclicAmbientGroup W p) :=
  (cyclicAmbientPointMulEquiv W p X).symm.toMonoidHom.comp
    ((cyclicPointGroup W p X).subtype.comp (cyclicPointMulEquiv W p X).toMonoidHom)

/-- The represented inclusion homomorphism is composition with the scheme map. -/
theorem cyclicFamilyPointInclusionHom_apply (X : Over (scalarQuotientModel W p).left)
    (f : X ⟶ cyclicFamilyModel W p) :
    cyclicFamilyPointInclusionHom W p X f = f ≫ cyclicFamilyInclusion W p := by
  apply (cyclicAmbientPointEquiv W p X).injective
  rw [cyclicFamilyInclusion_point]
  exact (cyclicAmbientPointMulEquiv W p X).apply_symm_apply _

/-- The actual incidence embedding is a morphism of group schemes. -/
instance cyclicFamilyInclusionIsMonHom : IsMonHom (cyclicFamilyInclusion W p) where
  one_hom := by
    have h := (cyclicFamilyPointInclusionHom W p (𝟙_ _)).map_one
    rw [cyclicFamilyPointInclusionHom_apply] at h
    simpa only [← MonObj.one_eq_one] using h
  mul_hom := by
    let C := cyclicFamilyModel W p
    have h := (cyclicFamilyPointInclusionHom W p (C ⊗ C)).map_mul (fst C C) (snd C C)
    simp only [cyclicFamilyPointInclusionHom_apply, Hom.mul_def, lift_fst_snd,
      Category.id_comp] at h
    refine h.trans ?_
    congr 1

omit [Fact p.Prime] in
/-- The subgroup map is the incidence embedding with its pullback factors exchanged. -/
theorem cyclicFamilyInclusion_left :
    (cyclicFamilyInclusion W p).left =
      cyclicIncidenceInclusion W p ≫
        (pullbackSymmetry (scalarQuotientModel W p).hom (torsionModel W p).hom).hom := by
  apply pullback.hom_ext
  · simp [cyclicFamilyInclusion, cyclicAmbientPointEquiv, 
      cyclicPointToTorsion]
  · simp [cyclicFamilyInclusion, cyclicAmbientPointEquiv, 
      cyclicPointToTorsion, cyclicIncidenceInclusion_toBase]

/-- The cyclic group embeds as a closed subgroup of the torsion scheme. -/
instance cyclicFamilyInclusionClosed : IsClosedImmersion (cyclicFamilyInclusion W p).left := by
  rw [cyclicFamilyInclusion_left]
  have := cyclicIncidenceInclusion_closed W p
  infer_instance

/-- The relative subgroup inclusion is a monomorphism. -/
instance cyclicFamilyInclusionMono : Mono (cyclicFamilyInclusion W p) :=
  Over.mono_of_mono_left _

end WeierstrassCurve.CubicCharts
