/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackCoproduct
public import FLT.Mazur.PolygonCyclicDivisor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Pullback of the constant cyclic divisor

Finite coproducts and the monoidal unit commute with arbitrary base change.
The comparison respects group multiplication. Combined with the actual
divisor-comap isomorphism, it identifies the pulled-back divisor group with
the constant cyclic group on the new base. The section-kernel product also
commutes with this pullback, retaining multiplicities.
-/

open CategoryTheory Limits AlgebraicGeometry MonObj MonoidalCategory
@[expose] public noncomputable section
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ConstantCyclicPullback
universe u
variable {S T : Scheme.{u}} (g : T ⟶ S) (n : ℕ) [NeZero n]
local notation "F" => Over.pullback g

/-- The constant cyclic scheme commutes with arbitrary base change. -/
def equivalence : ConstantCyclicGroup.model T n ≅ (F).obj (ConstantCyclicGroup.model S n) :=
  Sigma.mapIso (fun _ : ZMod n ↦ Functor.Monoidal.εIso (F)) ≪≫
    OverPullbackCoproduct.equivalence g (fun _ : ZMod n ↦ 𝟙_ (Over S))

/-- The comparison preserves each constant component section. -/
@[reassoc (attr := simp)]
theorem component_equivalence (i : ZMod n) :
    ConstantCyclicGroup.component T n i ≫ (equivalence g n).hom =
      (Functor.Monoidal.εIso (F)).hom ≫ (F).map (ConstantCyclicGroup.component S n i) := by
  simp [equivalence, ConstantCyclicGroup.component]
instance equivalence_isMonHom : IsMonHom (equivalence g n).hom where
  one_hom := by
    change ConstantCyclicGroup.identity T n ≫ (equivalence g n).hom = _
    rw [ConstantCyclicGroup.identity, Category.assoc, component_equivalence]
    change (𝟙 _) ≫ (Functor.Monoidal.εIso (F)).hom ≫
      (F).map (ConstantCyclicGroup.component S n 0) =
      (Functor.Monoidal.εIso (F)).hom ≫ (F).map ((𝟙 _) ≫ ConstantCyclicGroup.component S n 0)
    simp
  mul_hom := by
    apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n ↦ 𝟙_ (Over T))
      (fun _ : ZMod n ↦ 𝟙_ (Over T))
    intro i j
    change (ConstantCyclicGroup.component T n i ⊗ₘ ConstantCyclicGroup.component T n j) ≫
      ConstantCyclicGroup.multiplication T n ≫ (equivalence g n).hom = _
    rw [ConstantCyclicGroup.component_multiplication_assoc, component_equivalence,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, component_equivalence,
      component_equivalence]
    change μ[𝟙_ (Over T)] ≫ (Functor.Monoidal.εIso (F)).hom ≫
      (F).map (ConstantCyclicGroup.component S n (i + j)) =
      (((Functor.Monoidal.εIso (F)).hom ≫ (F).map (ConstantCyclicGroup.component S n i)) ⊗ₘ
        ((Functor.Monoidal.εIso (F)).hom ≫ (F).map (ConstantCyclicGroup.component S n j))) ≫
        Functor.LaxMonoidal.μ (F) _ _ ≫ (F).map (ConstantCyclicGroup.multiplication S n)
    rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc,
      ← Functor.map_comp, ConstantCyclicGroup.component_multiplication, Functor.map_comp]
    change (λ_ (𝟙_ (Over T))).hom ≫ Functor.LaxMonoidal.ε (F) ≫ _ =
      (Functor.LaxMonoidal.ε (F) ⊗ₘ Functor.LaxMonoidal.ε (F)) ≫
        Functor.LaxMonoidal.μ (F) _ _ ≫ (F).map (λ_ (𝟙_ (Over S))).hom ≫ _
    rw [Functor.LaxMonoidal.ε_tensorHom_comp_μ_assoc]
    simp
end FLT.Mazur.ConstantCyclicPullback
namespace FLT.Mazur.PolygonCyclicDivisorPullback
open PolygonPinching PolygonBoundaryDivisor FCurve
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "I" => ideal K n p (fun _ ↦ 1)

/-- The actual pulled-back divisor is the constant cyclic scheme over the new base. -/
def equivalence :
    Over.mk (((I).comap (pullback.fst C.hom g)).subschemeι ≫ pullback.snd C.hom g) ≅
      ConstantCyclicGroup.model T n :=
  divisorBaseChangeOverIso C.hom g (I) ≪≫
    (Over.pullback g).mapIso (PolygonCyclicDivisor.overIso K n p hn q h).symm ≪≫
    (ConstantCyclicPullback.equivalence g n).symm

/-- Pull back the divisor group, then transport to the actual comap subscheme. -/
abbrev grpObj : GrpObj
    (Over.mk (((I).comap (pullback.fst C.hom g)).subschemeι ≫ pullback.snd C.hom g)) := by
  letI := PolygonCyclicDivisor.grpObj K n p hn q h
  letI : GrpObj (Over.mk (pullback.snd ((I).subschemeι ≫ C.hom) g)) :=
    inferInstanceAs (GrpObj ((Over.pullback g).obj (PolygonCyclicDivisor.divisor K n p)))
  exact GrpObj.ofIso (divisorBaseChangeOverIso C.hom g (I)).symm

instance equivalence_isMonHom :
    letI := grpObj K n p hn q h g
    IsMonHom (equivalence K n p hn q h g).hom := by
  let := PolygonCyclicDivisor.grpObj K n p hn q h
  let : GrpObj (Over.mk (pullback.snd ((I).subschemeι ≫ C.hom) g)) :=
    inferInstanceAs (GrpObj ((Over.pullback g).obj (PolygonCyclicDivisor.divisor K n p)))
  let := grpObj K n p hn q h g
  have : IsMonHom (divisorBaseChangeOverIso C.hom g (I)).hom := by
    change IsMonHom (divisorBaseChangeOverIso C.hom g (I)).symm.inv
    infer_instance
  have : IsMonHom ((Over.pullback g).map (PolygonCyclicDivisor.overIso K n p hn q h).inv) := by
    infer_instance
  have : IsMonHom (ConstantCyclicPullback.equivalence g n).inv := by infer_instance
  dsimp only [equivalence, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  infer_instance

include h in
/-- The pulled-back ideal is the product of the pulled-back section kernels. -/
theorem ideal_pullback : (I).comap (pullback.fst C.hom g) =
    ∏ i, (sectionBaseChange C.hom g (PolygonMarkedSections.sectionMap K n p 1 i)
      (PolygonMarkedSections.section_base K n p 1 i)).ker := by
  let := PolygonSeparated.cocone K n hn p q h
  exact section_prod_comap_eq C.hom g Finset.univ _ _
end FLT.Mazur.PolygonCyclicDivisorPullback
