/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.FramedRepresentationRing
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The local completion of the framed representation ring

For a residual representation `ρ : G → GLₙ(k)`, this file constructs the maximal ideal
`m_ρ` of the framed coordinate algebra `O[G,n]`, localizes at `m_ρ`, and completes the
resulting Noetherian local ring at its maximal ideal. This is the algebraic backbone of the
finite-group construction in de Smit--Lenstra, Section 3.

Mathlib proves that the resulting completion is local and adically complete. Promoting it to
`ProartinianCat O` needs two further bridges not currently available as reusable theorems:
Noetherianity of the adic completion and the identification of its residue `O`-algebra with
`ResidueField O`. Those bridges, together with the continuous universal property, remain the
next part of dSL-2.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Deformation

noncomputable section

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type v) [Group G] [Finite G]
variable (n : Type w) [Fintype n] [DecidableEq n]

/-- A framed representation ring on finitely many variables over a Noetherian ring is
Noetherian. -/
noncomputable instance framedRepresentationRing_isNoetherian :
    IsNoetherianRing (FramedRepresentationRing O G n) := by
  let e := RingQuot.ringQuotEquivIdealQuotient (FramedRepresentationRelation O G n)
  exact isNoetherianRing_of_ringEquiv _ e.symm

variable (ρ : G →* GL n (ResidueField O))

/-- Evaluation of the framed coordinate algebra at the residual representation. -/
noncomputable def residualRepresentationHom :
    FramedRepresentationRing O G n →ₐ[O] ResidueField O :=
  FramedRepresentationRing.ofRepresentation ρ

omit [IsNoetherianRing O] [Finite G] in
/-- Evaluation at the residual representation is surjective because its restriction to `O`
is the residue map. -/
lemma residualRepresentationHom_surjective :
    Function.Surjective (residualRepresentationHom O G n ρ) := by
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  exact ⟨algebraMap O (FramedRepresentationRing O G n) a, by
    simp [residualRepresentationHom]⟩

/-- The maximal ideal of the framed coordinate algebra selected by `ρ`. -/
noncomputable def residualRepresentationIdeal : Ideal (FramedRepresentationRing O G n) :=
  RingHom.ker (residualRepresentationHom O G n ρ).toRingHom

noncomputable instance residualRepresentationIdeal_isMaximal :
    (residualRepresentationIdeal O G n ρ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (residualRepresentationHom_surjective O G n ρ)

/-- The localization of the framed coordinate algebra at the residual ideal. -/
abbrev FramedLocalRing :=
  Localization.AtPrime (residualRepresentationIdeal O G n ρ)

noncomputable instance framedLocalRing_isNoetherian :
    IsNoetherianRing (FramedLocalRing O G n ρ) := inferInstance

/-- The maximal-adic completion of the framed local ring. -/
noncomputable abbrev FramedCompletion : Type _ :=
  letI : CommRing (FramedLocalRing O G n ρ) := inferInstance
  AdicCompletion (maximalIdeal (FramedLocalRing O G n ρ)) (FramedLocalRing O G n ρ)

noncomputable instance framedCompletion_isLocalRing :
    IsLocalRing (FramedCompletion O G n ρ) := inferInstance

noncomputable instance framedCompletion_isAdicComplete :
    IsAdicComplete (maximalIdeal (FramedCompletion O G n ρ))
      (FramedCompletion O G n ρ) := inferInstance

/-- The universal matrix representation, transported first to the residual localization and then
to its maximal-adic completion. -/
noncomputable def universalFramedLift : G →* GL n (FramedCompletion O G n ρ) :=
  letI : CommRing (FramedLocalRing O G n ρ) := inferInstance
  (Matrix.GeneralLinearGroup.map
    ((algebraMap (FramedLocalRing O G n ρ)
      (AdicCompletion (maximalIdeal (FramedLocalRing O G n ρ))
        (FramedLocalRing O G n ρ))).comp
      (algebraMap (FramedRepresentationRing O G n) (FramedLocalRing O G n ρ)))).comp
    (universalRepresentation O G n)

end

end Deformation
