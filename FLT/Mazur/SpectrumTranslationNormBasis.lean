/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleTranslationNormCharts

/-!
# Finite bases on actual spectrum sections

Transport a coefficient basis to the original structural section algebra of
its spectrum. This identifies the algebra used by geometric translation norms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.EtaleTranslationBranch
open Approximation
universe u v
set_option backward.isDefEq.respectTransparency false
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap R B))
/-- Use the actual structural algebra on spectrum sections. -/
local instance spectrumSectionAlgebra : Algebra R Γ(Spec (.of B), ⊤) :=
  affineBaseSectionAlgebra g

/-- The canonical spectrum section equivalence respects the original base scalars. -/
def spectrumSectionAlgEquiv : B ≃ₐ[R] Γ(Spec (.of B), ⊤) :=
  { (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv with
    commutes' := by
      intro r
      have h := congrArg (fun k : CommRingCat.of R ⟶ Γ(Spec (.of B), ⊤) ↦ k r)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R B)))
      exact h }

/-- A finite basis of the coefficient algebra yields a basis of the actual section algebra. -/
def spectrumSectionBasis {ι : Type v} (b : Basis ι R B) :
    Basis ι R Γ(Spec (.of B), ⊤) :=
  b.map (spectrumSectionAlgEquiv R B).toLinearEquiv

end FLT.Mazur.EtaleTranslationBranch
