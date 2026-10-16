/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameAction

/-!
# Moving-endpoint actions on an exact invariant boundary

Pull back the boundary along the first endpoint of normalized frames. A Cartesian
original closed relation transports its whole scheme structure along every
normalized permutation, without reducing either the boundary or the test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

/-- The exact boundary of normalized frames, pulled back at the moving first endpoint. -/
def boundary : Scheme := pullback (first p q I o) i

/-- Retain the whole ambient normalized frame. -/
def inclusion : boundary (p := p) (q := q) I o i ⟶ source p q I o := pullback.fst _ _

/-- The original closed first endpoint, including its scheme structure. -/
def endpoint : boundary (p := p) (q := q) I o i ⟶ B := pullback.snd _ _

instance inclusion_mono : Mono (inclusion (p := p) (q := q) I o i) :=
  inferInstanceAs (Mono (pullback.fst _ _))

omit [Mono i] in
/-- The boundary is imposed by an exact Cartesian square. -/
theorem endpoint_condition :
    inclusion (p := p) (q := q) I o i ≫ first p q I o = endpoint I o i ≫ i :=
  pullback.condition

/-- The original transition arrow has its unique lift to the unchanged closed relation. -/
def transition (σ : Equiv.Perm I) : boundary (p := p) (q := q) I o i ⟶ C :=
  hr.lift (inclusion I o i ≫ actionArrow I o σ) (endpoint I o i) (by
    rw [Category.assoc, actionArrow_first, endpoint_condition])

omit [Mono i] in
/-- The closed transition retains the original moving arrow on all coefficients. -/
@[reassoc] theorem transition_arrow (σ : Equiv.Perm I) :
    transition (q := q) I o i z r hr σ ≫ z = inclusion I o i ≫ actionArrow I o σ :=
  hr.lift_fst _ _ _

omit [Mono i] in
/-- The closed transition begins at the exact original closed endpoint. -/
@[reassoc] theorem transition_first (σ : Equiv.Perm I) :
    transition (q := q) I o i z r hr σ ≫ r = endpoint I o i := hr.lift_snd _ _ _

omit [Mono i] in
include hs in
/-- The closed endpoint after rebasing is obtained from the original closed relation. -/
theorem transition_second (σ : Equiv.Perm I) :
    transition (q := q) I o i z r hr σ ≫ s ≫ i =
      inclusion I o i ≫ (action e I o σ).hom ≫ first p q I o := by
  rw [← hs, ← Category.assoc, transition_arrow, Category.assoc, actionArrow_second]

/-- The normalized action restricts to the exact pulled-back boundary. -/
def map (σ : Equiv.Perm I) :
    boundary (p := p) (q := q) I o i ⟶ boundary (p := p) (q := q) I o i :=
  pullback.lift (inclusion I o i ≫ (action e I o σ).hom)
    (transition (q := q) I o i z r hr σ ≫ s) (by
      simpa only [Category.assoc] using (transition_second e I o i z r s hr hs σ).symm)

omit [Mono i] in
/-- Boundary transport commutes with the actual moving-endpoint action. -/
@[reassoc] theorem map_inclusion (σ : Equiv.Perm I) :
    map e I o i z r s hr hs σ ≫ inclusion I o i =
      inclusion I o i ≫ (action e I o σ).hom := pullback.lift_fst _ _ _

omit [Mono i] in
/-- The first endpoint moves along the original closed relation, rather than staying fixed. -/
@[reassoc] theorem map_endpoint (σ : Equiv.Perm I) :
    map e I o i z r s hr hs σ ≫ endpoint I o i =
      transition (q := q) I o i z r hr σ ≫ s := pullback.lift_snd _ _ _

/-- Identity transport retains the full boundary scheme. -/
theorem map_one : map e I o i z r s hr hs 1 = 𝟙 _ := by
  apply (cancel_mono (inclusion I o i)).mp
  rw [map_inclusion, Category.id_comp]
  change inclusion I o i ≫ actionMap e I o 1 = inclusion I o i
  rw [actionMap_one, Category.comp_id]

/-- Boundary transport obeys the same multiplication law as the ambient action. -/
theorem map_mul (σ τ : Equiv.Perm I) :
    map e I o i z r s hr hs (σ * τ) =
      map e I o i z r s hr hs τ ≫ map e I o i z r s hr hs σ := by
  apply (cancel_mono (inclusion I o i)).mp
  rw [map_inclusion, Category.assoc, map_inclusion, ← Category.assoc, map_inclusion]
  change inclusion I o i ≫ actionMap e I o (σ * τ) =
    (inclusion I o i ≫ actionMap e I o τ) ≫ actionMap e I o σ
  rw [actionMap_mul, Category.assoc]

/-- Every permutation is an automorphism of the original pulled-back closed scheme. -/
def aut (σ : Equiv.Perm I) : Aut (boundary (p := p) (q := q) I o i) where
  hom := map e I o i z r s hr hs σ
  inv := map e I o i z r s hr hs σ⁻¹
  hom_inv_id := by rw [← map_mul, inv_mul_cancel, map_one]
  inv_hom_id := by rw [← map_mul, mul_inv_cancel, map_one]

/-- The finite permutation group acts on the exact original boundary. -/
def action : Equiv.Perm I →* Aut (boundary (p := p) (q := q) I o i) where
  toFun := aut e I o i z r s hr hs
  map_one' := by
    apply Aut.ext
    exact map_one e I o i z r s hr hs
  map_mul' σ τ := by
    apply Aut.ext
    exact map_mul e I o i z r s hr hs σ τ

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
