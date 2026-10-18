/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicPrescribedNeighborhood

/-!
# Both normalized charts cover prescribed generators on arbitrary smooth objects

The characteristic neighborhoods assemble into a small fppf cover. On every
member the actual atlas subgroup compares with the original full subgroup,
carrying the chosen atlas generator and all its powers to the prescribed ones.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- A small fppf cover by both actual charts retains the specified original generator. -/
theorem exists_prescribed_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange (q i))
        (H.baseChange (C.f i)),
        pullSection (q i) (normalizedGenerator n (b i)) ≫ a.subgroup.hom =
          pullSection (C.f i) P := by
  choose U g hg hl hx b q a ha using exists_prescribed_characteristic_neighborhood H hP
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, b, q, fun i ↦ ⟨a i, ha i⟩⟩

omit [Smooth E.curve.hom] in
/-- The same actual comparison retains every power of the specified original generator. -/
theorem prescribed_characteristic_generator_pow {T : Scheme} (g : T ⟶ S) (b : Bool)
    (q : T ⟶ normalizedLocus n b)
    (a : CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g))
    (ha : pullSection q (normalizedGenerator n b) ≫ a.subgroup.hom = pullSection g P)
    (m : ℕ) :
    (pullSection q (normalizedGenerator n b) ^ m) ≫ a.subgroup.hom =
      pullSection g (P ^ m) := by
  rw [MonObj.pow_comp, ha, section_pow]

end FLT.Mazur.CyclicCharacteristicAtlas
