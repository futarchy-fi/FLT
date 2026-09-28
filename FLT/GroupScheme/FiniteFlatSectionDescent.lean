/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatFiltration
public import FLT.GroupScheme.PadicBialgebraDescent

/-!
# Arithmetic descent of sections of finite-flat extensions

For an actual finite-flat extension over `ℤ[1/2]`, compatible sections over
`ℤ[1/6]` and `ℤ₃` descend to a section of its specified integral projection.
The theorem does not assume an integral splitting or replace the extension's
middle object. Constructing the compatible sections from a rational Galois
splitting remains a separate input.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.FiniteFlatExtension

open PadicPatching

local instance : Fact (¬ (3 : ℤ) ∣ 2) := ⟨by norm_num⟩

variable {A X Q : FiniteFlatObject ZInvTwo} (E : FiniteFlatExtension A X Q)

/-- Compatible local and away sections give a unique integral section of the
prescribed projection, with both prescribed restrictions. No flatness or
projectivity hypothesis beyond the original finite-flat models is added. -/
theorem existsUnique_section_of_away_local
    (sAway : Away 2 3 ⊗[ZInvTwo] X.model.CoordinateRing →ₐc[Away 2 3]
      Away 2 3 ⊗[ZInvTwo] Q.model.CoordinateRing)
    (sLocal : ℤ_[3] ⊗[ZInvTwo] X.model.CoordinateRing →ₐc[ℤ_[3]]
      ℤ_[3] ⊗[ZInvTwo] Q.model.CoordinateRing)
    (h : ∀ x : X.model.CoordinateRing,
      scalarExtensionMap (Away 2 3) ℚ_[3] Q.model.CoordinateRing
          (sAway (1 ⊗ₜ[ZInvTwo] x)) =
        scalarExtensionMap ℤ_[3] ℚ_[3] Q.model.CoordinateRing
          (sLocal (1 ⊗ₜ[ZInvTwo] x)))
    (hs : sAway.comp
      (Bialgebra.TensorProduct.map (BialgHom.id (Away 2 3) (Away 2 3)) E.quotient) =
        BialgHom.id (Away 2 3) (Away 2 3 ⊗[ZInvTwo] Q.model.CoordinateRing)) :
    ∃! s : Q.Hom X,
      s.comp E.quotient = BialgHom.id ZInvTwo Q.model.CoordinateRing ∧
      (∀ x, (1 : Away 2 3) ⊗ₜ[ZInvTwo] s x = sAway (1 ⊗ₜ[ZInvTwo] x)) ∧
      (∀ x, (1 : ℤ_[3]) ⊗ₜ[ZInvTwo] s x = sLocal (1 ⊗ₜ[ZInvTwo] x)) := by
  let : Module.FinitePresentation ZInvTwo Q.model.CoordinateRing :=
    Module.finitePresentation_of_finite ZInvTwo Q.model.CoordinateRing
  let : Module.Projective ZInvTwo Q.model.CoordinateRing :=
    Module.Flat.projective_of_finitePresentation
  exact existsUnique_bialgHom_section_of_away_local 3 2
    X.model.CoordinateRing Q.model.CoordinateRing E.quotient sAway sLocal h hs

end ThreeAdicPlan.FiniteFlatExtension
