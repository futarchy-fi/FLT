/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DenseGroundHilbertFullInterior
public import FLT.Mazur.AffineHilbertFullFiberPrincipal

/-!
# Affine principal refinement preserves original interior on dense ground

Prime avoidance retains the entire original orbit inside an affine principal
source. The constructed dense coefficient open then upgrades retained
fullness to interior membership for the NEW chart too. The coefficient is
not claimed invariant. Whole geometric maps and their original sections
are retained exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve AffineEtaleDenseFiniteGround
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]

/-- The principal refinement has an original full INTERIOR, not merely a full chosen fiber. -/
theorem exists_denseGround_principal_interior (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) (hb : A.hom x ∈ groundOpen R V) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨x, hr⟩ : (A.left.basicOpen r).toScheme) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) := by
  have hi := (denseGround_fullEnvelopeInterior_iff f hL d V c k x hb).mpr hx
  obtain ⟨r, hr, hsub, hf⟩ := exists_fullInterior_principal_chart f hL d V c k x hi
  refine ⟨r, hr, hsub, ?_⟩
  apply (denseGround_fullEnvelopeInterior_iff f hL d V c
    (orbitPrincipalChart f d V k r) ⟨x, hr⟩ ?_).mpr hf
  exact hb

/-- A geometric original parameter lifts to the affine refinement with exact class recovery. -/
theorem exists_denseGround_geometric_principal {K : Type} [Field K]
    {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
    (hx : b.left (default : Spec (.of K)) ∈ fullEnvelopeLocus f hL d V c k)
    (ht : t (default : Spec (.of K)) ∈ groundOpen R V) :
    ∃ (r : Γ(A.left, ⊤)) (b' : Over.mk t ⟶ orbitPrincipalSource r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      b' ≫ orbitPrincipalSourceMap r = b ∧
      b' ≫ orbitPrincipalChart f d V k r = b ≫ k ∧
      (relativeFppfSheaf f).obj.map b'.op
          (sectionAt f hL d V c (orbitPrincipalChart f d V k r)) =
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) ∧
      b'.left (default : Spec (.of K)) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) := by
  let η : Spec (.of K) := default
  have hb : A.hom (b.left η) ∈ groundOpen R V := by
    have hw := congrArg (fun g : Spec (.of K) ⟶ Spec (.of R) ↦ g η) b.w
    change A.hom (b.left η) = t η at hw
    rwa [hw]
  obtain ⟨r, hr, hsub, hi⟩ := exists_denseGround_principal_interior f hL d V c k _ hx hb
  have hbr : Set.range b.left ⊆ Set.range (A.left.basicOpen r).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim (α := Spec (.of K)) x η]
    exact hr
  let z := IsOpenImmersion.lift (A.left.basicOpen r).ι b.left hbr
  let b' : Over.mk t ⟶ orbitPrincipalSource r := Over.homMk z (by
    change z ≫ (A.left.basicOpen r).ι ≫ A.hom = t
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact b.w)
  have hc : b' ≫ orbitPrincipalSourceMap r = b :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hk : b' ≫ orbitPrincipalChart f d V k r = b ≫ k := by
    rw [orbitPrincipalChart, ← Category.assoc, hc]
  refine ⟨r, b', hsub, hc, hk, ?_, ?_⟩
  · change (relativeFppfSheaf f).obj.map b'.op
      ((relativeFppfSheaf f).obj.map (orbitPrincipalChart f d V k r).op
        (variableChartSection f hL d V c)) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hk,
      op_comp, Functor.map_comp]
    rfl
  · have he : b'.left η = (⟨b.left η, hr⟩ : (A.left.basicOpen r).toScheme) := by
      apply Subtype.ext
      exact congrArg (fun g : Over.mk t ⟶ A ↦ g.left η) hc
    rw [show (default : Spec (.of K)) = η from rfl, he]
    exact hi

end FLT.Mazur.HilbertChart.AffineRestriction
