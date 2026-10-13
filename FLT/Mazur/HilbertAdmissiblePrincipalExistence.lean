/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrincipalNormAdmissible

/-!
# Constructing nonvanishing admissible coefficients near full-interior points

Prime avoidance first retains the entire finite orbit in an affine principal
source. The regular norm on the nonaffine good open then supplies an actual
nonvanishing member of that new source's original invariant denominator ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
/-- The finite basis uses the original translation structural algebra. -/
local instance existenceNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))

include b
/-- Every original full-interior point yields a nonvanishing admissible invariant norm. -/
theorem exists_fullInterior_admissible_principal (x : A.left)
    (hx : x ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      ∃ s : compatibleFunctions
        (fst f hL d V c (orbitPrincipalChart f d V k r)).left
        (snd f hL d V c (orbitPrincipalChart f d V k r)).left,
        s ∈ invariantEnvelopeDenominators f hL d V c (orbitPrincipalChart f d V k r) ∧
        (⟨x, hr⟩ : (orbitPrincipalSource r).left) ∈
          (orbitPrincipalSource r).left.basicOpen s.val := by
  obtain ⟨r, hr, hsub, ho⟩ := exists_fullInterior_orbit_principal f hL d V c k x hx
  exact ⟨r, hr, hsub, orbitPrincipalAdmissibleNorm f hL d V c k r hsub b,
    orbitPrincipalAdmissibleNorm_mem f hL d V c k r hsub b,
    orbitPrincipalAdmissibleNorm_nonvanishing f hL d V c k r hsub b ⟨x, hr⟩ ho⟩

/-- The retained point now lies in the NEW full-fiber interior, not merely its full-fiber set. -/
theorem exists_fullInterior_principal_interior (x : A.left)
    (hx : x ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (r : Γ(A.left, ⊤)) (hr : x ∈ A.left.basicOpen r),
      A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k ∧
      (⟨x, hr⟩ : (orbitPrincipalSource r).left) ∈
        fullEnvelopeInterior f hL d V c (orbitPrincipalChart f d V k r) := by
  obtain ⟨r, hr, hsub, s, hs, hx'⟩ :=
    exists_fullInterior_admissible_principal f hL d V c k b x hx
  exact ⟨r, hr, hsub,
    (invariantDenominator_iff_fullEnvelopeInterior f hL d V c _ s).mp hs hx'⟩

end FLT.Mazur.HilbertChart.AffineRestriction
