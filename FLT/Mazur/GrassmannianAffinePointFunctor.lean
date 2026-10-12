/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismRecoveredPoint

/-!
# The natural affine functor of points of the glued Grassmannian scheme

The actual original Grassmannian functor is naturally isomorphic to the functor
of base-preserving affine tests of the glued scheme. The inverse uses effective
quotient descent and is natural under every coefficient algebra map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M κ : Type u} [CommRing R] [AddCommGroup M] [Module R M] [Fintype κ]
  {d : ℕ}

/-- Pullback of an actual base-preserving affine scheme test along a coefficient map. -/
def ambientSchemePointMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (s : A →ₐ[R] B)
    (f : {f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A}) :
    {f : Spec (.of B) ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R B} :=
  ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ f.val, by
    rw [Category.assoc, f.property, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact s.commutes⟩

/-- The glued scheme's actual affine functor of points over the original base. -/
def ambientGrassmannianAffinePointFunctor : CommAlgCat.{u} R ⥤ Type u where
  obj A := {f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
    f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A}
  map s := ↾(ambientSchemePointMap s.hom)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change Spec.map (𝟙 (.of A)) ≫ f.val = f.val
    simp only [Spec.map_id, Category.id_comp]
  map_comp s t := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom s.hom.toRingHom ≫
      CommRingCat.ofHom t.hom.toRingHom) ≫ f.val =
        Spec.map (CommRingCat.ofHom t.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom s.hom.toRingHom) ≫ f.val
    rw [Spec.map_comp, Category.assoc]

variable {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
  (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The original quotient functor is naturally represented on all affine coefficient tests. -/
def ambientGrassmannianAffineRepresentation :
    Module.Grassmannian.functor (R := R) (M := M) d ≅
      ambientGrassmannianAffinePointFunctor (R := R) (M := M) (κ := κ) (d := d) :=
  NatIso.ofComponents (fun A ↦ (ambientGrassmannianPointEquiv (A := A) b hκ).toIso)
    (fun s ↦ by
      apply ConcreteCategory.hom_ext
      intro N
      apply Subtype.ext
      exact ambientClassifyingMap_natural b N hκ s.hom)

include b hκ in
/-- Recovery is natural under every coefficient algebra map, without flatness restrictions. -/
theorem ambientMorphismPoint_natural {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (s : A →ₐ[R] B)
    (f : {f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A}) :
    ambientMorphismPoint (ambientSchemePointMap s f).val (ambientSchemePointMap s f).property =
      Module.Grassmannian.map s (ambientMorphismPoint f.val f.property) := by
  apply ambientClassifyingMap_injective b hκ
  dsimp only
  rw [ambientMorphismPoint_classifies, ambientClassifyingMap_natural,
    ambientMorphismPoint_classifies]
  rfl

end FLT.Mazur.GrassmannianChart
