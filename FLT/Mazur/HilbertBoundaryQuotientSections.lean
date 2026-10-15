/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryQuotient
public import FLT.Mazur.RelativeRelationClosedObstruction

/-!
# The original closed boundary's invariant section obstruction

The section obstruction is attached to the actual original boundary map,
using its full independent relation endpoints over the unchanged coefficient
base. Its vanishing is not assumed or proved. The top open supplies a concrete
affine source domain without requiring a quotient scheme chart.
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

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

local notation "Q" => locallyRingedQuotient («p» := p) («q» := q)
local notation "Qc" => locallyRingedQuotient («p» := r) («q» := s)
local notation "P" => locallyRingedProjection («p» := p) («q» := q)
local notation "Pc" => locallyRingedProjection («p» := r) («q» := s)

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

omit [Etale V.hom] [IsAffine A.left] in
/-- The first regular-function square uses the original whole relation map. -/
theorem originalClosedArrow_left_fst :
    (z).left ≫ (p).left = (r).left ≫ (i).left :=
  congrArg Over.Hom.left (originalClosedArrow_fst f hL d V c k)

/-- The second square retains the independent original endpoint. -/
theorem originalClosedArrow_left_snd :
    (z).left ≫ (q).left = (s).left ≫ (i).left :=
  congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)

/-- The full original boundary map in explicit invariant-sheaf coordinates. -/
def originalClosedInvariantMap : invariantLocallyRingedSpace ec ⟶
    invariantLocallyRingedSpace e :=
  invariantMap e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k)

local notation "m" => originalClosedInvariantMap f hL d V c k

/-- The invariant-coordinate map is the already constructed original quotient map. -/
@[reassoc]
theorem originalClosedInvariantMap_comparison :
    (invariantLocallyRingedIso ec).hom ≫ m =
      originalClosedQuotientMap f hL d V c k ≫ (invariantLocallyRingedIso e).hom := by
  let _ : Epi Pc := by
    dsimp only [locallyRingedProjection]
    infer_instance
  apply (cancel_epi Pc).mp
  rw [← Category.assoc]
  change invariantLocallyRingedProjection ec ≫ m = _
  rw [originalClosedQuotientMap_projection_assoc]
  exact invariantMap_projection e ec (i).left (z).left _ _

omit [Etale V.hom] [IsOpenImmersion k.left] in
/-- The top orbit open has the whole original affine source as inverse image. -/
theorem originalClosed_top_affine : IsAffineOpen (pullOpen e ⊤).val := by
  have h : (pullOpen e ⊤).val = ⊤ := by ext x; rfl
  rw [h]
  exact isAffineOpen_top A.left

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

/-- The actual obstruction group on any orbit open with affine original source domain. -/
abbrev originalClosedSectionObstructionGroup :=
  closedSectionObstructionGroup e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W

/-- The actual original boundary sheaf section has an explicit additive lifting obstruction. -/
def originalClosedSectionObstruction :
    (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W)) →+
      originalClosedSectionObstructionGroup f hL d V c k W :=
  closedSectionObstruction e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W hW

/-- Vanishing detects actual quotient section lifts, keeping the full original relation. -/
theorem originalClosedSectionObstruction_eq_zero_iff
    (t : (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    originalClosedSectionObstruction f hL d V c k W hW t = 0 ↔
      ∃ v : (invariantSheaf e).obj.obj (op W), (m).c.app (op W) v = t :=
  closedSectionObstruction_eq_zero_iff e ec (i).left (z).left _ _ W hW t

/-- Surjectivity of the original boundary comparison is exactly obstruction vanishing. -/
theorem originalClosedInvariantMap_surjective_iff :
    Function.Surjective ((m).c.app (op W)) ↔
      originalClosedSectionObstruction f hL d V c k W hW = 0 :=
  invariantMap_section_surjective_iff e ec (i).left (z).left _ _ W hW

/-- The exact additive image of the original boundary structure-sheaf comparison. -/
theorem originalClosedInvariantMap_section_range :
    ((m).c.app (op W)).hom.toAddMonoidHom.range =
      (originalClosedSectionObstruction f hL d V c k W hW).ker :=
  invariantMap_section_range e ec (i).left (z).left _ _ W hW

end FLT.Mazur.HilbertChart.AffineRestriction
