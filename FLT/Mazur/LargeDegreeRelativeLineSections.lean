/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCurveUniformAcyclicity
public import FLT.Mazur.ProperLinePushforwardLocalFree

/-!
# Relative line sections from a uniform numerical degree bound

For families obtained from a fixed pointed smooth proper integral curve, the
field-independent degree bound applies to the actual residue-algebra fibers.
It supplies the fiber acyclicity needed for positive relative vanishing and
finite free charts of the actual pushforward. Lines may vary on the family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve

/-- Projection from the actual residue-algebra fiber to its coefficient field spectrum. -/
abbrev residueAlgebraFiberProjection {X S : Scheme} [IsAffine S] (f : X ⟶ S)
    (z : PrimeSpectrum Γ(S, ⊤)) :=
  Limits.pullback.snd f (AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField)

variable {k : Type} [Field k] {C : Scheme} [IsIntegral C]
  (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- A single numerical bound constructs relative vanishing and local free direct images. -/
theorem pointedCurve_uniform_relative_sections (hd : topologicalKrullDim C = 1)
    (hc : HasConstantGlobalSections c)
    (s : Spec (.of k) ⟶ C) (hs : s ≫ c = 𝟙 _) :
    ∃ d : ℤ, ∀ (S : Scheme) [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
      (X : Scheme) (a : X ⟶ C) (f : X ⟶ S) (b : S ⟶ Spec (.of k)),
      IsPullback a f c b →
      (∀ z : PrimeSpectrum Γ(S, ⊤), IsIntegral (Limits.pullback f
        (AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField))) →
      ∀ L : X.Modules, LocallyFreeRankOne L →
      (∀ z : PrimeSpectrum Γ(S, ⊤), d ≤ curveSheafDegree
        (residueAlgebraFiberProjection f z) (residueAlgebraFiberLine f L z)) →
      (∀ n, Subsingleton (ModuleH L (n + 1))) ∧
        LocallyFiniteFree ((pushforward f).obj L) := by
  obtain ⟨d, hbound⟩ := pointedCurve_uniform_field_acyclicity c hd hc s hs
  refine ⟨d, ?_⟩
  intro S _ _ X a f b h hIntegral L hL hdeg
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  let _ : Flat f := MorphismProperty.of_isPullback h (inferInstance : Flat c)
  have hV (z : PrimeSpectrum Γ(S, ⊤)) (n : ℕ) :
      Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)) := by
    let g := AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField
    let _ := hIntegral z
    exact hbound z.asIdeal.ResidueField (Limits.pullback f g)
      (Limits.pullback.fst f g ≫ a) (Limits.pullback.snd f g) (g ≫ b)
      ((IsPullback.of_hasPullback f g).paste_horiz h)
      (residueAlgebraFiberLine f L z) (hL.pullback (Limits.pullback.fst f g)) (hdeg z) n
  exact ⟨positive_vanishing_of_residue_fibers f L hL hV,
    properLinePushforward_locallyFiniteFree f L hL hV⟩

end FLT.Mazur.LineSectionBaseChange
