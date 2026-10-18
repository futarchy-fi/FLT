/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedRelation
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# Descent from both characteristic charts using the actual unmarked relation

An invariant of full curve/subgroup comparisons descends along any actual
fppf presentation of an original modular object. Cross-characteristic
comparisons are included. Subcanonicity gives an actual scheme morphism,
independent of the presentation, with evaluation on every test parameter.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme}
  (v : ∀ b, normalizedLocus n b ⟶ Y)

/-- Invariance under actual unmarked comparisons, including different characteristic charts. -/
def UnmarkedInvariant : Prop :=
  ∀ (T : Scheme) (b c : Bool) (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c),
    UnmarkedRelated n b c q r → q ≫ v b = r ≫ v c

variable (hv : UnmarkedInvariant n v) {S : Scheme} (z : ampleCyclicClasses S n)
  (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
  (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i))
  (hq : ∀ i, (normalizedModuliMap n (b i)).app (Opposite.op (C.X i)) (ULift.up (q i)) =
    ampleCyclicClassesPullback (C.f i) n z)

include hv hq in
/-- The two actual charts glue an unmarked invariant to a unique morphism on the base. -/
theorem unmarkedInvariant_cover_descent :
    ∃! d : S ⟶ Y, ∀ i, C.f i ≫ d = q i ≫ v (b i) := by
  have hcompat : Presieve.Arrows.Compatible (yoneda.obj Y) C.f
      (fun i ↦ q i ≫ v (b i)) := by
    intro i j T a e hae
    change a ≫ q i ≫ v (b i) = e ≫ q j ≫ v (b j)
    simpa only [Category.assoc] using hv T (b i) (b j) (a ≫ q i) (e ≫ q j)
      (unmarkedRelated_overlap n (b i) (b j) z (C.f i) (C.f j)
        (q i) (q j) (hq i) (hq j) a e hae)
  have hy : Presieve.IsSheafFor (yoneda.obj Y) C.presieve₀ :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck C.mem₀)
  exact (Presieve.isSheafFor_arrows_iff _ _).mp hy _ hcompat

include hv hq in
/-- Descent evaluates on every chart representative after any base change. -/
theorem unmarkedInvariant_descent_evaluation (d : S ⟶ Y)
    (hd : ∀ i, C.f i ≫ d = q i ≫ v (b i))
    {T : Scheme} (g : T ⟶ S) (c : Bool) (r : T ⟶ normalizedLocus n c)
    (hr : (normalizedModuliMap n c).app (Opposite.op T) (ULift.up r) =
      ampleCyclicClassesPullback g n z) : g ≫ d = r ≫ v c := by
  let D := C.pullback₁ g
  have hy : Presieve.IsSheafFor (yoneda.obj Y) D.presieve₀ :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck D.mem₀)
  apply hy.isSeparatedFor.ext
  rintro U a ⟨i⟩
  change pullback.fst g (C.f i) ≫ g ≫ d = pullback.fst g (C.f i) ≫ r ≫ v c
  rw [← Category.assoc, pullback.condition, Category.assoc, hd]
  have he := hv _ (b i) c (pullback.snd g (C.f i) ≫ q i) (pullback.fst g (C.f i) ≫ r)
    (unmarkedRelated_overlap n (b i) c z (C.f i) g (q i) r (hq i) hr
      (pullback.snd g (C.f i)) (pullback.fst g (C.f i)) pullback.condition.symm)
  simpa only [Category.assoc] using he

include hv hq in
/-- Universal evaluation characterizes descent independently of the chosen covering family. -/
theorem unmarkedInvariant_unique_evaluation :
    ∃! d : S ⟶ Y, ∀ (T : Scheme) (g : T ⟶ S) (c : Bool) (r : T ⟶ normalizedLocus n c),
      (normalizedModuliMap n c).app (Opposite.op T) (ULift.up r) =
        ampleCyclicClassesPullback g n z → g ≫ d = r ≫ v c := by
  obtain ⟨d, hd, hu⟩ := unmarkedInvariant_cover_descent n v hv z C b q hq
  refine ⟨d, fun T g c r hr ↦
    unmarkedInvariant_descent_evaluation n v hv z C b q hq d hd g c r hr, ?_⟩
  intro e he
  exact hu e (fun i ↦ he (C.X i) (C.f i) (b i) (q i) (hq i))

include hv in
/-- Every original smooth ample cyclic object has a unique evaluation of an unmarked invariant. -/
theorem unmarkedInvariant_smooth_unique_evaluation {E : GeneralizedEllipticCurve S}
    [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple) :
    ∃! d : S ⟶ Y, ∀ (T : Scheme) (g : T ⟶ S) (c : Bool) (r : T ⟶ normalizedLocus n c),
      Nonempty (CompatibleIso ((normalizedSubgroup n c).baseChange r) (H.baseChange g)) →
        g ≫ d = r ≫ v c := by
  obtain ⟨C, b, q, hq⟩ := exists_normalized_moduli_fppf_cover n H hc ha
  obtain ⟨d, hd, hu⟩ := unmarkedInvariant_unique_evaluation n v hv
    (Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) C b q hq
  refine ⟨d, ?_, ?_⟩
  · intro T g c r hr
    apply hd T g c r
    rw [normalizedModuliMap_eq_pullback]
    exact Quotient.sound hr
  · intro e he
    apply hu e
    intro T g c r hr
    apply he T g c r
    rw [normalizedModuliMap_eq_pullback] at hr
    exact Quotient.exact hr

end FLT.Mazur.CyclicCharacteristicAtlas
