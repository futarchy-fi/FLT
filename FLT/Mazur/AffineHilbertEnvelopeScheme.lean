/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEnvelopeCoaction
public import FLT.Mazur.AffineAlgebraDescentScheme
public import FLT.Mazur.AffineBaseSectionFunctor

/-!
# Effective affine reconstruction for the original full-envelope Hilbert coaction

The spectrum of the original fixed coefficients is constructed. Flatness comes
from the translation base, and scalar extension reconstructs the original
parameter coefficients. The envelope-isomorphism hypothesis remains explicit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeRelationTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
local notation "β" => k ≫ variableHilbertBase f d V
/-- The parameter's original structural algebra. -/
local instance schemeSourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The translation base's original structural algebra. -/
local instance schemeBaseAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
variable [IsIso (toEnvelope f hL d V c k).left]

/-- The constructed spectrum of the original fixed coefficients. -/
def fullEnvelopeScheme : Scheme :=
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  AffineAlgebraDescent.descendedScheme (fullEnvelopeData f hL d V c k)

/-- The original affine parameter maps to the constructed invariant spectrum. -/
def fullEnvelopeProjection : A.left ⟶ fullEnvelopeScheme f hL d V c k :=
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  A.left.isoSpec.hom ≫ AffineAlgebraDescent.schemeProjection (fullEnvelopeData f hL d V c k)

/-- The constructed spectrum retains its original R-base map. -/
def fullEnvelopeBase : fullEnvelopeScheme f hL d V c k ⟶ Spec (.of R) :=
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  AffineAlgebraDescent.schemeBase (fullEnvelopeData f hL d V c k)

@[reassoc]
theorem fullEnvelopeProjection_base :
    fullEnvelopeProjection f hL d V c k ≫ fullEnvelopeBase f hL d V c k = A.hom := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  change A.left.isoSpec.hom ≫ AffineAlgebraDescent.schemeProjection
    (fullEnvelopeData f hL d V c k) ≫
      AffineAlgebraDescent.schemeBase (fullEnvelopeData f hL d V c k) = _
  rw [AffineAlgebraDescent.schemeProjection, AffineAlgebraDescent.schemeBase, ← Spec.map_comp]
  exact affineBaseSectionsSpecIso_over R A

omit f hL d c k [IsIso (toEnvelope f hL d V c k).left] [IsAffine A.left]
  [Algebra.FiniteType ℤ R] in
/-- Flatness of the translation scheme gives flatness over the ORIGINAL ring R. -/
theorem fullEnvelope_translation_flat [Flat V.hom] : Module.Flat R Γ(V.left, ⊤) := by
  apply RingHom.flat_algebraMap_iff.mp
  have h : (Scheme.ΓSpecIso (.of R)).inv.hom.Flat := RingHom.Flat.of_bijective
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective
  change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).Flat
  exact h.comp V.hom.flat_appTop

variable [Flat V.hom]

/-- Effective multiplicative descent reconstructs the ORIGINAL parameter coefficient algebra. -/
def fullEnvelopeReconstruction :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    Γ(V.left, ⊤) ⊗[R] AffineAlgebraDescent.invariants
      (fullEnvelopeData f hL d V c k) ≃ₐ[Γ(V.left, ⊤)]
       Γ(A.left, ⊤) := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  let _ := fullEnvelope_translation_flat V
  exact AffineAlgebraDescent.reconstruction (fullEnvelopeData f hL d V c k)

/-- Reconstruction is the actual scalar multiplication followed by the original fixed inclusion. -/
theorem fullEnvelopeReconstruction_tmul (s : Γ(V.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    ∀ b : AffineAlgebraDescent.invariants (fullEnvelopeData f hL d V c k),
      fullEnvelopeReconstruction f hL d V c k (s ⊗ₜ[R] b) = (β).left.appTop s * b.val := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  let _ := fullEnvelope_translation_flat V
  dsimp only
  intro b
  exact AffineAlgebraDescent.reconstruct_tmul (fullEnvelopeData f hL d V c k) s b

/-- The constructed spectrum has the ORIGINAL affine parameter as its base change. -/
theorem fullEnvelope_isPullback : IsPullback (fullEnvelopeProjection f hL d V c k)
    (β).left (fullEnvelopeBase f hL d V c k) V.hom := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  let _ := fullEnvelope_translation_flat V
  apply (AffineAlgebraDescent.scheme_isPullback (fullEnvelopeData f hL d V c k)).of_iso'
    A.left.isoSpec (Iso.refl _) V.left.isoSpec (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · exact Scheme.isoSpec_hom_naturality (β).left
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · exact affineBaseSectionsSpecIso_over R V

end FLT.Mazur.HilbertChart.AffineRestriction
