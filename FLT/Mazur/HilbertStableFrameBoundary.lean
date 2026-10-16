/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrderedStableNeighborhood
public import FLT.Mazur.HilbertBoundaryRelationTests
public import FLT.Mazur.FiniteGroupPullbackAction

/-!
# Original boundary lifting on stable affine frame neighborhoods

Restrict the free permutation action to an actual stable affine frame open.
Pull back the exact original boundary and lift every invariant boundary
section. Comparison with the whole original relation remains separate.
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
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]

local notation "i" => originalBoundarySourceMap f hL d V c k
variable (n : ℕ)
local notation "F" => fullRelationOrderedPoints f hL d V c k n
local notation "ρ" => fullRelationOrderedAction f hL d V c k n
local notation "hρ" => fullRelationOrderedAction_first f hL d V c k n
open RelativeOrderedTuples

variable (U : (fullRelationOrderedPoints f hL d V c k n).left.Opens)
  (hU : ∀ e : Equiv.Perm (Fin n),
    (fullRelationOrderedAction f hL d V c k n e).hom ⁻¹ᵁ U = U)

/-- The actual permutation action on the chosen stable affine test. -/
def stableFrameAction : Equiv.Perm (Fin n) →* Aut U.toScheme :=
  FiniteGroupRestriction.restrictedAction ρ U hU

omit [Etale V.hom] in
/-- The restricted automorphisms are the original ones after the actual open inclusion. -/
@[reassoc] theorem stableFrameAction_inclusion (e : Equiv.Perm (Fin n)) :
    (stableFrameAction f hL d V c k n U hU e).hom ≫ U.ι = U.ι ≫ (ρ e).hom :=
  FiniteGroupRestriction.restrictedAction_hom_ι ρ U hU e

omit [Etale V.hom] in
/-- Restricting the action retains the original first endpoint. -/
@[reassoc] theorem stableFrameAction_first (e : Equiv.Perm (Fin n)) :
    (stableFrameAction f hL d V c k n U hU e).hom ≫ U.ι ≫ (F).hom = U.ι ≫ (F).hom := by
  rw [← Category.assoc, stableFrameAction_inclusion,
    Category.assoc, fullRelationOrderedAction_first]

omit [Etale V.hom] in
/-- The restricted action stays free on every field-valued test. -/
theorem stableFrameAction_free (K : Type) [Field K] (a : Spec (.of K) ⟶ U.toScheme)
    (e : Equiv.Perm (Fin n))
    (he : a ≫ (stableFrameAction f hL d V c k n U hU e).hom = a) : e = 1 := by
  apply fullRelationOrderedAction_free f hL d V c k n K (a ≫ U.ι) e
  have h := congrArg (fun z ↦ z ≫ U.ι) he
  rw [Category.assoc, stableFrameAction_inclusion,
    ← Category.assoc] at h
  exact h

omit [Etale V.hom] in
/-- Restricting the action still permutes every independent original second endpoint. -/
@[reassoc] theorem stableFrameAction_second (e : Equiv.Perm (Fin n)) (a : Fin n) :
    (stableFrameAction f hL d V c k n U hU e).hom ≫
      U.ι ≫ fullRelationOrderedSecond f hL d V c k n a =
        U.ι ≫ fullRelationOrderedSecond f hL d V c k n (e.symm a) := by
  rw [← Category.assoc, stableFrameAction_inclusion,
    Category.assoc, fullRelationOrderedAction_second]

/-- The exact original boundary on the stable affine frame open. -/
def stableFrameBoundary : Scheme := pullback (U.ι ≫ (F).hom) (i).left

/-- The closed inclusion retains the original boundary ideal and nilpotents. -/
def stableFrameBoundaryInclusion : stableFrameBoundary f hL d V c k n U ⟶ U.toScheme :=
  pullback.fst (U.ι ≫ (F).hom) (i).left

instance stableFrameBoundaryInclusion_closed :
    IsClosedImmersion (stableFrameBoundaryInclusion f hL d V c k n U) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst (U.ι ≫ (F).hom) (i).left))

/-- The induced action on the exact original closed pullback. -/
def stableFrameBoundaryAction :
    Equiv.Perm (Fin n) →* Aut (stableFrameBoundary f hL d V c k n U) :=
  FiniteGroupPullback.action (stableFrameAction f hL d V c k n U hU)
    (U.ι ≫ (F).hom) (stableFrameAction_first f hL d V c k n U hU) (i).left

omit [Etale V.hom] in
/-- The actual original boundary inclusion is equivariant. -/
@[reassoc] theorem stableFrameBoundary_equivariant (e : Equiv.Perm (Fin n)) :
    (stableFrameBoundaryAction f hL d V c k n U hU e).hom ≫
      stableFrameBoundaryInclusion f hL d V c k n U =
        stableFrameBoundaryInclusion f hL d V c k n U ≫
          (stableFrameAction f hL d V c k n U hU e).hom :=
  FiniteGroupPullback.action_fst _ _ _ _ e

local notation "τ" => stableFrameAction f hL d V c k n U hU
local notation "σ" => stableFrameBoundaryAction f hL d V c k n U hU
local notation "j" => stableFrameBoundaryInclusion f hL d V c k n U
local notation "hj" => stableFrameBoundary_equivariant f hL d V c k n U hU

omit [Etale V.hom] in
/-- Every invariant section of the exact original boundary lifts on an affine stable frame test. -/
theorem stableFrameBoundary_invariantMap_surjective (ha : IsAffineOpen U) :
    Function.Surjective (SchemeFiniteGroupQuotient.invariantMap σ τ j hj) := by
  let _ : IsAffine U.toScheme := ha
  exact SchemeFiniteGroupQuotient.invariantMap_surjective_of_free τ
    (stableFrameAction_free f hL d V c k n U hU) σ j hj

omit [Etale V.hom] in
/-- Every invariant boundary section has an actual finite coefficient identity on this test. -/
theorem stableFrameBoundary_certificate (ha : IsAffineOpen U)
    (t : SchemeFiniteGroupQuotient.invariantCoordinates σ) :
    ∃ a : sectionLiftIdeal
        (SchemeFiniteGroupQuotient.invariantMap σ τ j hj) t →₀
          Γ(stableFrameBoundary f hL d V c k n U, ⊤),
      a.sum (fun v b ↦ b *
        (SchemeFiniteGroupQuotient.invariantMap σ τ j hj v.val).val) = 1 := by
  let _ : IsAffine U.toScheme := ha
  exact SchemeFiniteGroupQuotient.invariant_boundary_certificate_of_free τ
    (stableFrameAction_free f hL d V c k n U hU) σ j hj t

end FLT.Mazur.HilbertChart.AffineRestriction
