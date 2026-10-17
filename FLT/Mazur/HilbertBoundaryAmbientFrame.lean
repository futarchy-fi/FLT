/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryAmbientPresentation

/-!
# A constructed finite ambient boundary kernel frame

Noetherianity of the actual source constructs one finite ideal frame on the
whole orbit domain. Each original boundary section has a chosen ambient
lift; every other lift differs by a finite combination of this same frame.
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

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

set_option quotPrecheck false
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Q" => (sourceSheaf e).obj.obj (op W)
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)

local notation "D₀" => (invariantSheaf ec).obj.obj (op Wc)
local notation "r₀" => originalAmbientBoundaryRestriction f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryRestriction
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

include hW in
/-- The actual ambient boundary kernel admits a finite generating family. -/
theorem originalAmbientBoundary_exists_frame :
    ∃ (n : ℕ) (v : Fin n → Q), Ideal.span (Set.range v) = RingHom.ker r₀ :=
  Submodule.fg_iff_exists_fin_generating_family.mp
    (originalAmbientBoundary_kernel_fg f hL d V c k W hW)

/-- Number of generators chosen from the actual ambient boundary ideal. -/
def originalAmbientBoundaryFrameSize : ℕ :=
  (originalAmbientBoundary_exists_frame f hL d V c k W hW).choose

/-- A finite generating family of the actual boundary ideal. -/
def originalAmbientBoundaryFrame :
    Fin (originalAmbientBoundaryFrameSize f hL d V c k W hW) → Q :=
  (originalAmbientBoundary_exists_frame f hL d V c k W hW).choose_spec.choose

/-- The chosen frame generates exactly the ambient boundary kernel. -/
theorem originalAmbientBoundaryFrame_span :
    Ideal.span (Set.range (originalAmbientBoundaryFrame f hL d V c k W hW)) =
      RingHom.ker r₀ :=
  (originalAmbientBoundary_exists_frame f hL d V c k W hW).choose_spec.choose_spec

attribute [local irreducible] originalAmbientBoundaryFrameSize originalAmbientBoundaryFrame

/-- Each selected equation vanishes on the whole original boundary source. -/
theorem originalAmbientBoundaryFrame_restrict
    (j : Fin (originalAmbientBoundaryFrameSize f hL d V c k W hW)) :
    r₀ (originalAmbientBoundaryFrame f hL d V c k W hW j) = 0 := by
  apply RingHom.mem_ker.mp
  rw [← originalAmbientBoundaryFrame_span f hL d V c k W hW]
  exact Ideal.subset_span (Set.mem_range_self j)

/-- A chosen ambient lift of an arbitrary original invariant boundary section. -/
def originalAmbientBoundaryLift (t : D₀) : Q :=
  (originalAmbientBoundaryRestriction_surjective f hL d V c k W hW
    ((invariantInclusion ec).hom.app (op Wc) t)).choose

/-- The chosen ambient lift restricts exactly, including nilpotents. -/
theorem originalAmbientBoundaryLift_restrict (t : D₀) :
    r₀ (originalAmbientBoundaryLift f hL d V c k W hW t) =
      (invariantInclusion ec).hom.app (op Wc) t :=
  (originalAmbientBoundaryRestriction_surjective f hL d V c k W hW
    ((invariantInclusion ec).hom.app (op Wc) t)).choose_spec

end FLT.Mazur.HilbertChart.AffineRestriction
