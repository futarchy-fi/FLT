/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryRelationTests

/-!
# The original closed Picard kernel pair

The closed boundary relation represents equality of the original Picard
sections on every test. Reflexivity, symmetry and composition are scheme
morphisms, with no quotient effectivity assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

attribute [local irreducible] originalClosedRelation originalClosedFst originalClosedSnd
  originalClosedArrow originalBoundarySource originalBoundarySourceMap
local notation "σ" => originalClosedSection f hL d V c k

/-- Equal original classes along the closed relation remain equal after any test map. -/
theorem originalClosed_class_natural {T : Over (Spec (.of R))} (a : T ⟶ C) :
    (relativeFppfSheaf f).obj.map (a ≫ r).op σ =
      (relativeFppfSheaf f).obj.map (a ≫ s).op σ := by
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg ((relativeFppfSheaf f).obj.map a.op) (originalClosed_equal_class f hL d V c k)

/-- The full presheaf kernel pair of the original section on the closed boundary. -/
theorem originalClosed_isPullback : IsPullback (uliftYoneda.{1}.map r) (uliftYoneda.{1}.map s)
    ((uliftYonedaEquiv (F := (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)).symm σ)
    ((uliftYonedaEquiv (F := (relativeFppfSheaf f).obj ⋙ forget CommGrpCat)).symm σ) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro a
    exact originalClosed_class_natural f hL d V c k a.down
  · intro a b h
    exact ULift.ext (originalClosed_hom_ext f hL d V c k
      (congrArg ULift.down h.1) (congrArg ULift.down h.2))
  · intro a b h
    obtain ⟨w, hw, _⟩ := originalClosed_lift f hL d V c k a.down b.down h
    exact ⟨ULift.up w, ULift.ext hw.1, ULift.ext hw.2⟩

/-- The unique closed arrow with the prescribed equal-class endpoints. -/
def originalClosedTestArrow {T : Over (Spec (.of R))} (a b : T ⟶ B)
    (h : (relativeFppfSheaf f).obj.map a.op σ = (relativeFppfSheaf f).obj.map b.op σ) :
    T ⟶ C := (originalClosed_lift f hL d V c k a b h).choose

/-- The first whole closed endpoint is retained. -/
@[reassoc]
theorem originalClosedTestArrow_fst {T : Over (Spec (.of R))} (a b : T ⟶ B) (h) :
    originalClosedTestArrow f hL d V c k a b h ≫ r = a :=
  (originalClosed_lift f hL d V c k a b h).choose_spec.1.1

/-- The independent second whole closed endpoint is retained. -/
@[reassoc]
theorem originalClosedTestArrow_snd {T : Over (Spec (.of R))} (a b : T ⟶ B) (h) :
    originalClosedTestArrow f hL d V c k a b h ≫ s = b :=
  (originalClosed_lift f hL d V c k a b h).choose_spec.1.2

/-- Transitivity holds on the full scheme of composable closed arrows. -/
theorem originalClosed_composable_class :
    (relativeFppfSheaf f).obj.map (pullback.fst s r ≫ r).op σ =
      (relativeFppfSheaf f).obj.map (pullback.snd s r ≫ s).op σ := by
  rw [originalClosed_class_natural f hL d V c k (pullback.fst s r), pullback.condition]
  exact originalClosed_class_natural f hL d V c k (pullback.snd s r)

/-- The full original closed relation is an internal scheme equivalence relation. -/
def originalClosedEquivalence : CategoryTheory.EquivalenceRelation r s where
  right_cancellation _ _ _ h₁ h₂ := originalClosed_hom_ext f hL d V c k h₁ h₂
  «r» := originalClosedTestArrow f hL d V c k (𝟙 _) (𝟙 _) rfl
  reflexivity₁ := originalClosedTestArrow_fst f hL d V c k _ _ _
  reflexivity₂ := originalClosedTestArrow_snd f hL d V c k _ _ _
  «s» := originalClosedTestArrow f hL d V c k s r (originalClosed_equal_class f hL d V c k).symm
  symmetry₁ := originalClosedTestArrow_fst f hL d V c k _ _ _
  symmetry₂ := originalClosedTestArrow_snd f hL d V c k _ _ _
  c := PullbackCone.mk (pullback.fst s r) (pullback.snd s r) pullback.condition
  isLimit := pullbackIsPullback s r
  t := originalClosedTestArrow f hL d V c k (pullback.fst s r ≫ r) (pullback.snd s r ≫ s)
    (originalClosed_composable_class f hL d V c k)
  transitivity₁ := originalClosedTestArrow_fst f hL d V c k _ _ _
  transitivity₂ := originalClosedTestArrow_snd f hL d V c k _ _ _

/-- Closed reflexivity retains the original diagonal scheme morphism. -/
@[reassoc]
theorem originalClosedEquivalence_refl_arrow :
    (originalClosedEquivalence f hL d V c k).r ≫ z = i ≫ (equivalence f hL d V c k).r := by
  apply hom_ext f hL d V c k <;>
    simp only [Category.assoc, originalClosedArrow_fst, originalClosedArrow_snd,
      (originalClosedEquivalence f hL d V c k).reflexivity₁_assoc,
      (originalClosedEquivalence f hL d V c k).reflexivity₂_assoc,
      (equivalence f hL d V c k).reflexivity₁,
      (equivalence f hL d V c k).reflexivity₂,
      Category.comp_id]

/-- Closed symmetry retains the original inversion scheme morphism. -/
@[reassoc]
theorem originalClosedEquivalence_swap_arrow :
    (originalClosedEquivalence f hL d V c k).s ≫ z = z ≫ (equivalence f hL d V c k).s := by
  apply hom_ext f hL d V c k <;>
    simp only [Category.assoc, originalClosedArrow_fst, originalClosedArrow_snd,
      (originalClosedEquivalence f hL d V c k).symmetry₁_assoc,
      (originalClosedEquivalence f hL d V c k).symmetry₂_assoc,
      (equivalence f hL d V c k).symmetry₁,
      (equivalence f hL d V c k).symmetry₂]

end FLT.Mazur.HilbertChart.AffineRestriction
