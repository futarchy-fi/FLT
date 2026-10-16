/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionLiftCertificateEquiv
public import FLT.Mazur.SchemeRelationCoefficientDiagram
public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.RelativeRelationInvariantMapSections

/-!
# Original invariant sheaf sections in structural coefficient coordinates

On the whole source, invariant sheaf sections identify with the full algebra
of original endpoint equations. The comparison retains source inclusion and
commutes with maps of whole relations over the same coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]
  {A D A' D' : Over (Spec (.of R))} {p q : D ⟶ A} {p' q' : D' ⟶ A'}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Global sections retain the algebra of the original structural morphism. -/
local instance sectionAlgebra (Y : Over (Spec (.of R))) : Algebra R Γ(Y.left, ⊤) :=
  affineBaseSectionAlgebra Y.hom

/-- Whole invariant-sheaf sections are the actual full original coefficient equalizer. -/
def topCoefficientEquiv : (invariantSheaf e).obj.obj (op ⊤) ≃+*
    SchemeRelationCoefficientDiagram.invariants p q := by
  let E := invariantSectionRingEquiv e ⊤
  have h : originalInvariantSections (p := p) (q := q) (pullOpen e ⊤).val
      (pullOpen_preimage_eq e ⊤) =
        (SchemeRelationCoefficientDiagram.invariants p q).toSubring := by
    ext a
    change Γ(A.left, ⊤) at a
    change p.left.appTop a = q.left.appLE ⊤ ⊤ _ a ↔
      p.left.appTop a = q.left.appTop a
    simp [Scheme.Hom.appLE]
  exact E.trans (RingEquiv.subringCongr h)

/-- The coefficient equivalence is literally the original invariant inclusion. -/
theorem topCoefficientEquiv_val (a : (invariantSheaf e).obj.obj (op ⊤)) :
    (topCoefficientEquiv e a).val = (invariantInclusion e).hom.app (op ⊤) a := rfl

variable (e' : CategoryTheory.EquivalenceRelation p' q')
  (i : A' ⟶ A) (z : D' ⟶ D) (hp : z ≫ p = p' ≫ i) (hq : z ≫ q = q' ≫ i)
local notation "hp'" => congrArg Over.Hom.left hp
local notation "hq'" => congrArg Over.Hom.left hq
local notation "m" => invariantMap e e' i.left z.left hp' hq'

/-- The geometric map on whole invariant sections in unchanged source coordinates. -/
def topInvariantPullback : (invariantSheaf e).obj.obj (op ⊤) →+*
    (invariantSheaf e').obj.obj (op ⊤) := (m).c.app (op ⊤) |>.hom

/-- The full coefficient diagram is the actual sheaf pullback, not a substitute map. -/
theorem topCoefficientEquiv_natural (a : (invariantSheaf e).obj.obj (op ⊤)) :
    topCoefficientEquiv e' (topInvariantPullback e e' i z hp hq a) =
      SchemeRelationCoefficientDiagram.invariantMap p q p' q' i z hp hq
        (topCoefficientEquiv e a) := by
  apply Subtype.ext
  change (invariantInclusion e').hom.app (op ⊤)
    ((m).c.app (op ⊤) a) = i.left.appTop ((invariantInclusion e).hom.app (op ⊤) a)
  have h := invariantMap_source_apply e e' i.left z.left hp' hq' ⊤ a
  change (invariantInclusion e').hom.app (op ⊤)
    ((m).c.app (op ⊤) a) = i.left.appLE ⊤ ⊤ _
      ((invariantInclusion e).hom.app (op ⊤) a) at h
  simpa [Scheme.Hom.appLE] using h

/-- Certification in whole coefficient coordinates is precisely original sheaf certification. -/
theorem topCoefficient_certified_iff (t : (invariantSheaf e').obj.obj (op ⊤)) :
    topCoefficientEquiv e' t ∈ sourceCertifiedSections
      (SchemeRelationCoefficientDiagram.invariantMap p q p' q' i z hp hq).toRingHom
      (SchemeRelationCoefficientDiagram.invariants p' q').val.toRingHom ↔
    t ∈ sourceCertifiedSections (topInvariantPullback e e' i z hp hq)
      ((invariantInclusion e').hom.app (op ⊤)).hom :=
  SectionLiftCertificateEquiv.certified_iff _ _ _ _
    (topCoefficientEquiv e) (topCoefficientEquiv e') (RingEquiv.refl _)
    (fun a ↦ (topCoefficientEquiv_natural e e' i z hp hq a).symm) (fun _ ↦ rfl) t

end FLT.Mazur.RelativeRelationOrbit
