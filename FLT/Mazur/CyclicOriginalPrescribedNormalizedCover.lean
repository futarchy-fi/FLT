/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalPrescribedNormalizedNeighborhood

/-!
# Fppf normalized covers retain a prescribed original Cartier generator

The local original cubic construction supplies a small fppf cover by actual
even normalized subgroup charts. Every comparison retains the specified
generator, and hence every power, in the actual original subgroup carrier.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (h₂ : IsUnit (2 : Γ(S, ⊤)))

include hP h₂ in
/-- Actual normalized subgroups cover the original object with its specified generator. -/
theorem exists_prescribed_normalized_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n false),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n false).baseChange (q i))
        (H.baseChange (C.f i)),
        pullSection (q i) (evenNormalizedGenerator n) ≫ a.subgroup.hom =
          pullSection (C.f i) P := by
  have hx (x : S) := H.exists_prescribed_normalized_neighborhood hP h₂
    (V := ⊤) (x := x) (by trivial)
  choose U g hg hl hxg _ q a ha using hx
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hxg x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, q, fun i ↦ ⟨a i, ha i⟩⟩

omit [Smooth E.curve.hom] in
/-- The same full comparison retains all powers of the prescribed generator. -/
theorem prescribed_normalized_generator_pow {T : Scheme} (g : T ⟶ S)
    (q : T ⟶ normalizedLocus n false)
    (a : CompatibleIso ((normalizedSubgroup n false).baseChange q) (H.baseChange g))
    (ha : pullSection q (evenNormalizedGenerator n) ≫ a.subgroup.hom = pullSection g P)
    (m : ℕ) :
    (pullSection q (evenNormalizedGenerator n) ^ m) ≫ a.subgroup.hom =
      pullSection g (P ^ m) := by
  rw [MonObj.pow_comp, ha, section_pow]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
