/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientPointCover
public import FLT.Mazur.GrassmannianAmbientCommonTest

/-!
# A global scheme classifying morphism for every original ambient quotient

The actual coefficient principal cover carries compatible local classifications.
Gluing constructs a morphism into the ambient Grassmannian scheme over the original
base, uniquely characterized on every member of that cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
  (N : Module.Grassmannian A (A ⊗[R] M) d) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The principal-cover classifications agree on their entire categorical intersections. -/
theorem ambientPointCoverClassifyingMap_compatible
    (p q : AmbientPointCoverIndex (κ := κ) N) :
    pullback.fst ((ambientPointPrincipalCover b N hκ).f p)
        ((ambientPointPrincipalCover b N hκ).f q) ≫ ambientPointCoverClassifyingMap N p =
      pullback.snd ((ambientPointPrincipalCover b N hκ).f p)
        ((ambientPointPrincipalCover b N hκ).f q) ≫ ambientPointCoverClassifyingMap N q := by
  exact ambientGluedChartPoint_commonTest
    (IsScalarTower.toAlgHom R A (Localization.Away p.2.val))
    (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) N p.1 q.1
    (ambientPointCoverChartPoint N p) (ambientPointCoverChartPoint N q) rfl rfl
    _ _ pullback.condition

/-- The constructed global classifying map of the entire original quotient. -/
def ambientClassifyingMap : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d :=
  (ambientPointPrincipalCover b N hκ).glueMorphisms
    (ambientPointCoverClassifyingMap N) (ambientPointCoverClassifyingMap_compatible b N hκ)

/-- Every principal local classification is the restriction of the constructed global map. -/
@[reassoc] theorem ambientClassifyingMap_local (p : AmbientPointCoverIndex (κ := κ) N) :
    Spec.algebraMap A (Localization.Away p.2.val) ≫ ambientClassifyingMap b N hκ =
      ambientPointCoverClassifyingMap N p :=
  (ambientPointPrincipalCover b N hκ).ι_glueMorphisms _ _ p

/-- The constructed global map retains the original coefficient-base structure. -/
@[reassoc] theorem ambientClassifyingMap_over :
    ambientClassifyingMap b N hκ ≫ ambientGrassmannianStructure R M κ d =
      Spec.algebraMap R A := by
  apply (ambientPointPrincipalCover b N hκ).hom_ext
  intro p
  change Spec.algebraMap A (Localization.Away p.2.val) ≫ _ = _
  refine (ambientClassifyingMap_local_assoc b N hκ p _).trans
    ((ambientPointCoverClassifyingMap_over N p).trans ?_)
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The local classifications uniquely determine a global morphism. -/
theorem ambientClassifyingMap_unique
    (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
    (hf : ∀ p : AmbientPointCoverIndex (κ := κ) N,
      Spec.algebraMap A (Localization.Away p.2.val) ≫ f = ambientPointCoverClassifyingMap N p) :
    f = ambientClassifyingMap b N hκ := by
  apply (ambientPointPrincipalCover b N hκ).hom_ext
  intro p
  exact (hf p).trans (ambientClassifyingMap_local b N hκ p).symm

/-- The global morphism is independent of the ambient basis used only to prove coverage. -/
theorem ambientClassifyingMap_basis_independent {ι' : Type u} [Fintype ι']
    (b' : Module.Basis ι' R M) (hκ' : Fintype.card κ = Fintype.card ι' - d) :
    ambientClassifyingMap b N hκ = ambientClassifyingMap b' N hκ' := by
  apply ambientClassifyingMap_unique
  exact ambientClassifyingMap_local b N hκ

/-- A quotient already in a global chart has its original chart classification. -/
theorem ambientClassifyingMap_ofChart (i : AmbientChartIndex R M κ d)
    (P : AmbientChartPoint (ambientChartBaseChange A i)) :
    ambientClassifyingMap b P.val hκ = ambientGluedChartPoint i P := by
  symm
  apply ambientClassifyingMap_unique
  intro p
  let f := IsScalarTower.toAlgHom R A (Localization.Away p.2.val)
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ambientGluedChartPoint i P = _
  rw [← ambientGluedChartPoint_natural]
  exact ambientGluedChartPoint_eq i p.1 (ambientChartMap f i P)
    (ambientPointCoverChartPoint P.val p) rfl

end FLT.Mazur.GrassmannianChart
