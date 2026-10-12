/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicOriginalNormalizedCoverage
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# An actual fppf atlas for original smooth etale cyclic objects

Choose one proved normalized neighborhood at each base point. These form a
small fppf covering family, and every parameter represents the original class.
No finite subcover or global affineness hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  [Etale H.carrier.hom] (hc : H.IsCyclic) (ha : H.IsAmple)
  (h₂ : IsUnit (2 : Γ(S, ⊤))) (hn : Nat.Coprime 4 n)

include h₂ hn in
/-- The original object admits a small fppf family of actual full normalized parameters. -/
theorem exists_normalized_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (p : ∀ i : C.I₀, C.X i ⟶ cyclicNormalizedSlice n),
      ∀ i, (cyclicNormalizedSliceModuliMap n).app (Opposite.op (C.X i)) (ULift.up (p i)) =
        ampleCyclicClassesPullback (C.f i) n (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) := by
  have h (x : S) := exists_original_normalized_neighborhood H hc ha h₂ hn
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hx hV p hp using h
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, p, hp⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
