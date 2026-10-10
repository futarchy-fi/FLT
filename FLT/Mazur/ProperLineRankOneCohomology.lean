/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineRankOneDirectImage
public import FLT.Mazur.SpectrumFieldCohomologyCoordinates

/-!
# The rank-one open is the actual geometric H0 dimension-one locus

Canonical affine section base change and the original derived H0 comparison
compute the open's membership on every field-valued test. Positive fiber
cohomology vanishes by the original residue-fiber hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients SpectrumFieldCohomologyCoordinates
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {K : Type} [Field K] {P : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ Spec (.of K)} {g : Spec (.of K) ⟶ S}
  (h : IsPullback p q f g)

include h hL hV in
/-- The original rank equals actual H0 dimension on any field-valued test family. -/
theorem properLineSectionRank_fieldFiber (t : Spec (.of K)) :
    Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)
        (S.isoSpec.hom (g t)) =
      Module.finrank K (ModuleScalarH q ((pullback p).obj L) 0) := by
  let _ := globalSectionsField K
  have he := congrArg (fun a : Spec (.of K) ⟶ Spec Γ(S, ⊤) ↦ a t)
    (Scheme.isoSpec_hom_naturality g)
  change PrimeSpectrum.comap g.appTop.hom ((Spec (.of K)).isoSpec.hom t) =
    S.isoSpec.hom (g t) at he
  rw [← he, ← properLineSectionRank_baseChange f L hL hV h]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (ringHZeroBaseSections ((pullback p).obj L) q.appTop.hom).finrank_eq.symm.trans
    (cohomology_finrank q ((pullback p).obj L) 0)

include h hL hV in
/-- The actual rank-one open tests for geometric H0 dimension one, over every field. -/
theorem properLineRankOneOpen_field_iff (t : Spec (.of K)) :
    g t ∈ properLineRankOneOpen f L hL hV ↔
      Module.finrank K (ModuleScalarH q ((pullback p).obj L) 0) = 1 := by
  rw [mem_properLineRankOneOpen, properLineSectionRank_fieldFiber f L hL hV h t]

include h hL hV in
/-- The same field-valued family has no positive cohomology. -/
theorem properLine_fieldFiber_positive_vanishing (n : ℕ) :
    Subsingleton (ModuleScalarH q ((pullback p).obj L) (n + 1)) := by
  exact @Function.Injective.subsingleton _ _ _
    (moduleScalarHAddEquiv q ((pullback p).obj L) (n + 1)).injective
    (baseChange_vanishing_of_residue_fibers f L hL hV h n)

end FLT.Mazur.LineSectionBaseChange
