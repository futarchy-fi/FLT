/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryPrescribedCover
public import FLT.Mazur.CyclicCharacteristicRetainedFullParameter

/-!
# Actual full faithful parameters on the smooth characteristic cover

For an etale original cyclic subgroup, both characteristic charts retain
the prescribed generator and independent original auxiliary frame. If the
cyclic order is coprime to three and four, these give actual faithful product
parameters on the same cover, with all original evaluations unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open AuxiliaryLevel
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}

/-- The original smooth group is separated because it is open in a proper curve. -/
local instance faithfulFullCoverGroupSeparated {T : Scheme} (f : T ⟶ S) :
    IsSeparated (E.baseChange f).group.hom := by
  let _ : IsProper (E.baseChange f).curve.hom := (E.baseChange f).family.family.1
  rw [← (E.baseChange f).inclusion.w]
  infer_instance

variable [Smooth E.curve.hom] {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (h₄ : Nat.Coprime 4 n) (h₃ : Nat.Coprime 3 n)

include hP h₄ h₃ in
/-- The actual characteristic cover has faithful full parameters with exact original sections. -/
theorem exists_faithful_full_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ (E.baseChange (C.f i)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange (q i))
          (H.baseChange (C.f i)),
        (∀ j, pullSection (q i) (normalizedAuxiliaryMarking n (b i) j) ≫
          a.curve.hom.group = m i j) ∧
        pullSection (q i) (normalizedGenerator n (b i)) ≫ a.subgroup.hom =
          pullSection (C.f i) P ∧
        ∃ t : 𝟙_ (Over (C.X i)) ⟶ faithfulScheme (E.baseChange (C.f i)).group
            (Labels (normalizedAuxiliaryOrder (b i)) × Multiplicative (ZMod n)),
          ∀ j k, t ≫ faithfulInclusion _ _ ≫ value _ _ (j, k) =
            m i j * (H.baseChange (C.f i)).generatorCurveMarking (hP.baseChange H (C.f i)) k := by
  obtain ⟨C, b, m, q, hq⟩ := exists_auxiliary_prescribed_characteristic_fppf_cover H hP
  refine ⟨C, b, m, q, fun i ↦ ?_⟩
  obtain ⟨_, a, hm, ha⟩ := hq i
  let _ : Etale (H.baseChange (C.f i)).carrier.hom :=
    inferInstanceAs (Etale (CategoryTheory.Limits.pullback.snd H.carrier.hom (C.f i)))
  have hc : Nat.Coprime (normalizedAuxiliaryOrder (b i)) n := by
    cases b i
    · exact h₄
    · exact h₃
  refine ⟨a, hm, ha, retainedFullParameter (H.baseChange (C.f i))
    (hP.baseChange H (C.f i)) (b i) (q i) a (m i) hm hc, ?_⟩
  intro j k
  exact retainedFullParameter_value (H.baseChange (C.f i))
    (hP.baseChange H (C.f i)) (b i) (q i) a (m i) hm hc j k

end FLT.Mazur.CyclicCharacteristicAtlas
