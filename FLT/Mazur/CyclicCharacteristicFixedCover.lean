/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryPrescribedNeighborhood

/-!
# Prescribed generators on a specified characteristic chart

When the required integer is invertible, every member of the cover uses the
specified chart. This permits actual comparisons between different auxiliary
characteristics on their common domain, without an etaleness assumption on
the cyclic subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The integer required to use a specified auxiliary characteristic chart. -/
def chartInteger : Bool → ℕ
  | false => 2
  | true => 3

variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (b : Bool) (hb : IsUnit (chartInteger b : Γ(S, ⊤)))

include hP hb in
/-- A specified chart gives actual fppf neighborhoods retaining the original generator. -/
theorem exists_fixed_characteristic_neighborhood (x : S) :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g ∧ ∃ q : U ⟶ normalizedLocus n b,
        ∃ a : CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g),
          pullSection q (normalizedGenerator n b) ≫ a.subgroup.hom = pullSection g P := by
  cases b
  · obtain ⟨U, g, hf, hl, hx, _, _, _, q, a, _, ha⟩ :=
      H.exists_auxiliary_prescribed_normalized_neighborhood hP hb (V := ⊤) (x := x)
        (by trivial)
    exact ⟨U, g, hf, hl, hx, q, a, ha⟩
  · obtain ⟨U, g, hf, hl, hx, _, _, _, q, a, _, ha⟩ :=
      OddWeierstrassParameter.exists_auxiliary_prescribed_normalized_neighborhood H hP hb
        (V := ⊤) (x := x) (by trivial)
    exact ⟨U, g, hf, hl, hx, q, a, ha⟩

include hP hb in
/-- A small fppf cover uses only the specified chart and retains the prescribed generator. -/
theorem exists_fixed_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n b),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n b).baseChange (q i))
          (H.baseChange (C.f i)),
        pullSection (q i) (normalizedGenerator n b) ≫ a.subgroup.hom =
          pullSection (C.f i) P := by
  choose U g hf hl hx q a ha using exists_fixed_characteristic_neighborhood H hP b hb
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hf x, hl x⟩)
  exact ⟨C, q, fun i ↦ ⟨a i, ha i⟩⟩

end FLT.Mazur.CyclicCharacteristicAtlas
