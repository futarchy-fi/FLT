/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertChartRelation

/-!
# Original Picard kernel pairs on affine parameter restrictions

The constructed restricted relation is the full presheaf kernel pair. Its
reflexivity, inverse, and composition are actual scheme morphisms obtained
from equality of the original Picard sections on arbitrary tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "σ" => sectionAt f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- Equality of the two original classes survives any test map into the full relation. -/
theorem equal_class_natural {T : Over (Spec (.of R))} (a : T ⟶ relation f hL d V c k) :
    (relativeFppfSheaf f).obj.map (a ≫ p).op σ =
      (relativeFppfSheaf f).obj.map (a ≫ q).op σ := by
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg ((relativeFppfSheaf f).obj.map a.op) (equal_class f hL d V c k)

/-- The full presheaf kernel pair of the ORIGINAL restricted Picard section. -/
theorem isPullback : IsPullback (uliftYoneda.{1}.map p) (uliftYoneda.{1}.map q)
    ((uliftYonedaEquiv (F := (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)).symm σ)
    ((uliftYonedaEquiv (F := (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)).symm σ) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro z
    exact equal_class_natural f hL d V c k z.down
  · intro a b h
    exact ULift.ext (hom_ext f hL d V c k
      (congrArg ULift.down h.1) (congrArg ULift.down h.2))
  · intro a b h
    obtain ⟨z, hz, _⟩ := lift f hL d V c k a.down b.down h
    exact ⟨ULift.up z, ULift.ext hz.1, ULift.ext hz.2⟩

/-- The unique actual relation morphism of equal-class endpoints. -/
def arrow {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (h : (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ) :
    T ⟶ relation f hL d V c k := (lift f hL d V c k a b h).choose

/-- The constructed arrow has the original first endpoint. -/
@[reassoc]
theorem arrow_fst {T : Over (Spec (.of R))} (a b : T ⟶ A) (h) :
    arrow f hL d V c k a b h ≫ p = a := (lift f hL d V c k a b h).choose_spec.1.1

/-- The constructed arrow has the original second endpoint. -/
@[reassoc]
theorem arrow_snd {T : Over (Spec (.of R))} (a b : T ⟶ A) (h) :
    arrow f hL d V c k a b h ≫ q = b := (lift f hL d V c k a b h).choose_spec.1.2

/-- Transitivity is proved on the actual scheme of composable original relation arrows. -/
theorem composable_class :
    (relativeFppfSheaf f).obj.map (pullback.fst q p ≫ p).op σ =
      (relativeFppfSheaf f).obj.map (pullback.snd q p ≫ q).op σ := by
  rw [equal_class_natural f hL d V c k (pullback.fst q p), pullback.condition]
  exact equal_class_natural f hL d V c k (pullback.snd q p)

/-- The full relation on the restricted parameter scheme is an internal equivalence relation. -/
def equivalence : CategoryTheory.EquivalenceRelation p q where
  right_cancellation _ _ _ h₁ h₂ := hom_ext f hL d V c k h₁ h₂
  r := arrow f hL d V c k (𝟙 _) (𝟙 _) rfl
  reflexivity₁ := arrow_fst f hL d V c k _ _ _
  reflexivity₂ := arrow_snd f hL d V c k _ _ _
  s := arrow f hL d V c k q p (equal_class f hL d V c k).symm
  symmetry₁ := arrow_fst f hL d V c k _ _ _
  symmetry₂ := arrow_snd f hL d V c k _ _ _
  c := PullbackCone.mk (pullback.fst q p) (pullback.snd q p) pullback.condition
  isLimit := pullbackIsPullback q p
  t := arrow f hL d V c k (pullback.fst q p ≫ p) (pullback.snd q p ≫ q)
    (composable_class f hL d V c k)
  transitivity₁ := arrow_fst f hL d V c k _ _ _
  transitivity₂ := arrow_snd f hL d V c k _ _ _

/-- The actual inverse is a scheme isomorphism, retaining both endpoints. -/
def swapIso : relation f hL d V c k ≅ relation f hL d V c k where
  hom := (equivalence f hL d V c k).s
  inv := (equivalence f hL d V c k).s
  hom_inv_id := by
    apply hom_ext f hL d V c k <;>
      simp only [Category.assoc, (equivalence f hL d V c k).symmetry₁,
        (equivalence f hL d V c k).symmetry₂, Category.id_comp]
  inv_hom_id := by
    apply hom_ext f hL d V c k <;>
      simp only [Category.assoc, (equivalence f hL d V c k).symmetry₁,
        (equivalence f hL d V c k).symmetry₂, Category.id_comp]

end FLT.Mazur.HilbertChart.AffineRestriction
