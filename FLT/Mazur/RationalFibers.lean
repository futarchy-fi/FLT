/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FCurveContracts

/-!
# Rational sections and finite fibers

A section over a field is determined by its underlying point. The section equation
makes the embedding of its residue field into the base field inverse to the base
map. Thus two sections with the same point have the same residue-field map.

The rational fiber of a finite morphism injects into its finite topological fiber.
This proves the two rational-point contracts of C8 in `docs/FCURVE_CONTRACTS.md`
over arbitrary fields, without a dimension or closed-subset assumption.

The proof uses `Scheme.SpecToEquivOfField` for the residue-field factorization
and `Scheme.Hom.finite_preimage_singleton` for topological fibers. The stronger
quasi-compact locally quasi-finite version and finite-set preimage lemma are
included for consumers. No algebraic closure or finite-type assumption is
needed for the injectivity of rational sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur

namespace Sections

variable {K : Type u} [Field K]
variable {X Y Z : Over (Spec (CommRingCat.of K))}

/-- The underlying point of a rational section. -/
def point (a : Sections X) : X.left := a.left (IsLocalRing.closedPoint K)

/-- Every point of the source spectrum has the same image. -/
theorem apply_eq_point (a : Sections X) (s : Spec (CommRingCat.of K)) :
    a.left s = point a := by
  rw [Subsingleton.elim s (IsLocalRing.closedPoint K)]
  rfl

/-- The point map commutes with a morphism over the field. -/
@[simp]
theorem point_map (f : X ⟶ Y) (a : Sections X) :
    point (map f a) = f.left (point a) := rfl

/-- Composition in the over category has the same underlying point formula. -/
@[simp]
theorem point_comp (a : Sections X) (f : X ⟶ Y) :
    point (a ≫ f) = f.left (point a) := rfl

/-- The field embedding belonging to a rational section. -/
def residueMap (a : Sections X) : X.left.residueField (point a) ⟶ CommRingCat.of K :=
  (Scheme.SpecToEquivOfField K X.left a.left).2

/-- Recover a section from its point and its residue-field embedding. -/
@[reassoc (attr := simp)]
theorem residueMap_fromSpecResidueField (a : Sections X) :
    Spec.map (residueMap a) ≫ X.left.fromSpecResidueField (point a) = a.left :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X.left a.left

/-- The base field maps to the residue field at any point. -/
def baseResidueMap (x : X.left) : CommRingCat.of K ⟶ X.left.residueField x :=
  Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom)

/-- The base residue map represents the composite to the base scheme. -/
@[simp]
theorem specMap_baseResidueMap (x : X.left) :
    Spec.map (baseResidueMap x) = X.left.fromSpecResidueField x ≫ X.hom :=
  Spec.map_preimage _

/-- The section equation gives a retraction on residue fields. -/
@[reassoc (attr := simp)]
theorem baseResidueMap_residueMap (a : Sections X) :
    baseResidueMap (point a) ≫ residueMap a = 𝟙 (CommRingCat.of K) := by
  apply Spec.map_injective
  simp only [Spec.map_comp, specMap_baseResidueMap, Spec.map_id,
    residueMap_fromSpecResidueField_assoc, Over.w, Over.mk_hom]

/-- At a rational point the residue embedding is also a section of the base map. -/
@[reassoc (attr := simp)]
theorem residueMap_baseResidueMap (a : Sections X) :
    residueMap a ≫ baseResidueMap (point a) = 𝟙 _ := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply (residueMap a).hom.injective
  have h := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom
    ((residueMap a).hom r)) (baseResidueMap_residueMap a)
  exact h

/-- The residue field at a rational section is canonically the base field. -/
def residueIso (a : Sections X) : X.left.residueField (point a) ≅ CommRingCat.of K where
  hom := residueMap a
  inv := baseResidueMap (point a)
  hom_inv_id := residueMap_baseResidueMap a
  inv_hom_id := baseResidueMap_residueMap a

/-- Rational sections are determined by their underlying point, over any field. -/
theorem point_injective : Function.Injective (point (X := X)) := by
  intro a b h
  apply Over.OverMorphism.ext
  apply (Scheme.SpecToEquivOfField K X.left).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨h, ?_⟩
  change residueMap a = (X.left.residueFieldCongr h).hom ≫ residueMap b
  have hb := baseResidueMap_residueMap b
  have ha := residueMap_baseResidueMap a
  have hc : baseResidueMap (point a) ≫ (X.left.residueFieldCongr h).hom =
      baseResidueMap (point b) := by
    generalize point a = x, point b = y at h ⊢
    subst y
    simp
  calc
    residueMap a = residueMap a ≫ baseResidueMap (point b) ≫ residueMap b := by
      rw [hb, Category.comp_id]
    _ = (X.left.residueFieldCongr h).hom ≫ residueMap b := by
      rw [← hc, ← Category.assoc, ← Category.assoc, ha, Category.id_comp]

/-- Equality of rational sections can be checked on their underlying points. -/
@[simp]
theorem point_eq_iff {a b : Sections X} : point a = point b ↔ a = b :=
  point_injective.eq_iff

/-- A section extensionality lemma with the point displayed explicitly. -/
theorem ext_of_point_eq {a b : Sections X} (h : point a = point b) : a = b :=
  point_injective h

/-- Rational sections embed into the underlying space. -/
def pointEmbedding : Sections X ↪ X.left where
  toFun := point
  inj' := point_injective

/-- A finite underlying space has only finitely many rational sections. -/
theorem finite_of_finite_space [Finite X.left] : Finite (Sections X) :=
  Finite.of_injective point point_injective

/-- Rational images agree exactly when their underlying image points agree. -/
theorem map_eq_iff (f : X ⟶ Y) (a b : Sections X) :
    map f a = map f b ↔ f.left (point a) = f.left (point b) :=
  point_eq_iff.symm

/-- Injectivity on underlying points implies injectivity on rational sections. -/
theorem map_injective (f : X ⟶ Y) (hf : Function.Injective f.left) :
    Function.Injective (map f) := by
  intro a b h
  apply point_injective
  exact hf (congrArg point h)

/-- The rational sections in one fiber, retaining their over-base equations. -/
abbrev Fiber (f : X ⟶ Y) (y : Sections Y) := {x : Sections X // map f x = y}

/-- A rational fiber maps into the corresponding topological fiber. -/
def fiberPoint (f : X ⟶ Y) (y : Sections Y) (x : Fiber f y) :
    f.left ⁻¹' {point y} :=
  ⟨point x.val, congrArg point x.property⟩

/-- The fiber point map is the restriction of the section point map. -/
@[simp]
theorem fiberPoint_val (f : X ⟶ Y) (y : Sections Y) (x : Fiber f y) :
    (fiberPoint f y x).val = point x.val := rfl

/-- The rational fiber injects into the topological fiber. -/
theorem fiberPoint_injective (f : X ⟶ Y) (y : Sections Y) :
    Function.Injective (fiberPoint f y) := by
  intro a b h
  exact Subtype.ext (point_injective (congrArg Subtype.val h))

/-- An explicit embedding suitable for counting rational fibers. -/
def fiberPointEmbedding (f : X ⟶ Y) (y : Sections Y) :
    Fiber f y ↪ (f.left ⁻¹' {point y}) where
  toFun := fiberPoint f y
  inj' := fiberPoint_injective f y

/-- A finite topological fiber suffices for finiteness of a rational fiber. -/
theorem finite_fiber_of_finite_preimage (f : X ⟶ Y) (y : Sections Y)
    (h : (f.left ⁻¹' {point y}).Finite) : Finite (Fiber f y) := by
  let := h.to_subtype
  exact Finite.of_injective (fiberPoint f y) (fiberPoint_injective f y)

/-- Quasi-compact locally quasi-finite maps have finite rational fibers. -/
theorem finite_fiber (f : X ⟶ Y) [LocallyQuasiFinite f.left] [QuasiCompact f.left]
    (y : Sections Y) : Finite (Fiber f y) :=
  finite_fiber_of_finite_preimage f y (f.left.finite_preimage_singleton (point y))

/-- Finitely many target sections have finitely many underlying points. -/
theorem finite_point_image {s : Set (Sections X)} (hs : s.Finite) :
    (point '' s).Finite := hs.image point

/-- The point of a section over a finite target set lies over one of its points. -/
theorem point_mem_preimage_image (f : X ⟶ Y) {s : Set (Sections Y)}
    {a : Sections X} (ha : map f a ∈ s) : point a ∈ f.left ⁻¹' (point '' s) :=
  ⟨map f a, ha, point_map f a⟩

/-- Preimages of finite sets of rational sections are finite for quasi-finite maps. -/
theorem finite_preimage (f : X ⟶ Y) [LocallyQuasiFinite f.left] [QuasiCompact f.left]
    {s : Set (Sections Y)} (hs : s.Finite) : ((map f) ⁻¹' s).Finite := by
  refine Set.Finite.of_injOn ?_ point_injective.injOn
    (f.left.finite_preimage (finite_point_image hs))
  intro a ha
  exact point_mem_preimage_image f ha

/-- Two field-valued scheme maps with the same base equation and point agree. -/
theorem hom_ext_of_point_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    {a b : Spec (CommRingCat.of K) ⟶ T}
    (ha : a ≫ t = 𝟙 _) (hb : b ≫ t = 𝟙 _)
    (h : a (IsLocalRing.closedPoint K) = b (IsLocalRing.closedPoint K)) : a = b := by
  let a' : Sections (Over.mk t) := Over.homMk a ha
  let b' : Sections (Over.mk t) := Over.homMk b hb
  exact congrArg Over.Hom.left (point_injective (a₁ := a') (a₂ := b') h)

end Sections

namespace FCurve

variable {K : Type u} [Field K]
variable {X Y : Over (Spec (CommRingCat.of K))}

/-- Distinct rational images give distinct underlying image points. -/
theorem distinctSectionImages (f : X ⟶ Y) (a b : Sections X) :
    DistinctSectionImages f a b := by
  intro h
  refine ⟨Sections.point a, Sections.point b, ?_⟩
  exact fun e => h (Sections.point_injective e)

/-- A finite morphism has finite fibers on rational sections. -/
theorem finiteRationalFibers (f : X ⟶ Y) : FiniteRationalFibers f := by
  intro hf y
  let := hf
  exact Sections.finite_fiber f y

/-- A finite set of rational target sections has finite rational preimage. -/
theorem finiteRationalPreimage (f : X ⟶ Y) [IsFinite f.left]
    {s : Set (Sections Y)} (hs : s.Finite) :
    {x : Sections X | x ≫ f ∈ s}.Finite :=
  Sections.finite_preimage f hs

end FCurve

end FLT.Mazur
