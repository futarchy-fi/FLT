/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeFppfRepresentativeOpenOverlap
public import FLT.Mazur.SchemeFppfOpenDescent

/-!
# Actual acyclic test opens for unpointed Picard-sheaf sections

Choose an actual fppf family of representatives, then descend their
intrinsic class opens. The recovery theorem works for every independently
supplied representative on every further test, so the result does not depend
on the choices or on a section of the original family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- A small actual fppf family on which the supplied section has relative representatives. -/
def finiteTypeFppfRepresentativeCover :
    Scheme.Cover.{0} Scheme.fppfPrecoverage T.left :=
  (relativeFppfClass_exists_cover f T s).choose

/-- A relative representative on each member of the actual covering family. -/
def finiteTypeFppfRepresentativeClass (i : (finiteTypeFppfRepresentativeCover f T s).I₀) :
    RelativePic (Limits.pullback.snd f
      (relativeCoverMember T (finiteTypeFppfRepresentativeCover f T s) i).hom) :=
  ((relativeFppfClass_exists_cover f T s).choose_spec i).choose

/-- Each chosen representative maps to the original restricted sheaf section. -/
theorem finiteTypeFppfRepresentativeClass_spec
    (i : (finiteTypeFppfRepresentativeCover f T s).I₀) :
    relativeFppfClass f _ (finiteTypeFppfRepresentativeClass f T s i) =
      (relativeFppfSheaf f).obj.map
        (relativeCoverArrow T (finiteTypeFppfRepresentativeCover f T s) i).op s :=
  ((relativeFppfClass_exists_cover f T s).choose_spec i).choose_spec

variable [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- The descended actual open of an arbitrary section, without an original section. -/
def finiteTypeUnpointedFppfAcyclicOpen : T.left.Opens :=
  SchemeFppfOpen.descend (finiteTypeFppfRepresentativeCover f T s) (fun i ↦
    finiteTypeRelativeClassOpen f
      (relativeCoverMember T (finiteTypeFppfRepresentativeCover f T s) i)
      (finiteTypeFppfRepresentativeClass f T s i))

/-- Every independent representative on every further test recovers this exact open. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_representative
    {U : Over (Spec (.of R))} (b : U ⟶ T)
    (c : RelativePic (Limits.pullback.snd f U.hom))
    (hc : relativeFppfClass f U c = (relativeFppfSheaf f).obj.map b.op s) :
    b.left ⁻¹ᵁ finiteTypeUnpointedFppfAcyclicOpen f T s =
      finiteTypeRelativeClassOpen f U c := by
  apply SchemeFppfOpen.preimage_descend
  intro i
  exact finiteTypeFppfRepresentativeOpen_pullback f
    (relativeCoverArrow T (finiteTypeFppfRepresentativeCover f T s) i) b s
    (finiteTypeFppfRepresentativeClass f T s i) c
    (finiteTypeFppfRepresentativeClass_spec f T s i) hc

/-- For a globally represented section the descended open is exactly its intrinsic class open. -/
theorem finiteTypeUnpointedFppfAcyclicOpen_class
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    finiteTypeUnpointedFppfAcyclicOpen f T (relativeFppfClass f T c) =
      finiteTypeRelativeClassOpen f T c := by
  simpa using finiteTypeUnpointedFppfAcyclicOpen_representative f T
    (relativeFppfClass f T c) (𝟙 T) c (by simp)

end FLT.Mazur.CartierAbel
