/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedModuliInvariantDescent

/-!
# Universal evaluation of a descended original modular invariant

The descended morphism evaluates correctly on every normalized representative
of the original class after any base change. This removes dependence on the
chosen covering family and its auxiliary markings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme} (v : cyclicNormalizedSlice n ⟶ Y)
  (hv : CyclicModuliInvariant n v) {S : Scheme} (c : ampleCyclicClasses S n)
  (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S)
  (p : ∀ i : C.I₀, C.X i ⟶ cyclicNormalizedSlice n)
  (hp : ∀ i, (cyclicNormalizedSliceModuliMap n).app (Opposite.op (C.X i))
    (ULift.up (p i)) = ampleCyclicClassesPullback (C.f i) n c)

include hv hp

/-- Every test representative gives the same value as the descended base morphism. -/
theorem cyclicModuliInvariant_descent_evaluation (d : S ⟶ Y)
    (hd : ∀ i, C.f i ≫ d = p i ≫ v)
    {T : Scheme} (g : T ⟶ S) (q : T ⟶ cyclicNormalizedSlice n)
    (hq : (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up q) =
      ampleCyclicClassesPullback g n c) : g ≫ d = q ≫ v := by
  let D := C.pullback₁ g
  have hy : Presieve.IsSheafFor (yoneda.obj Y) D.presieve₀ :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck D.mem₀)
  apply hy.isSeparatedFor.ext
  rintro U a ⟨i⟩
  change pullback.fst g (C.f i) ≫ g ≫ d = pullback.fst g (C.f i) ≫ q ≫ v
  rw [← Category.assoc, pullback.condition, Category.assoc, hd]
  have he := hv _ (pullback.snd g (C.f i) ≫ p i) (pullback.fst g (C.f i) ≫ q)
    (cyclicNormalizedSliceModuliMap_overlap n c (C.f i) g (p i) q (hp i) hq
      (pullback.snd g (C.f i)) (pullback.fst g (C.f i)) pullback.condition.symm)
  simpa only [Category.assoc] using he

/-- The universal evaluation property characterizes a unique morphism from the original base. -/
theorem cyclicModuliInvariant_unique_evaluation :
    ∃! d : S ⟶ Y, ∀ (T : Scheme) (g : T ⟶ S) (q : T ⟶ cyclicNormalizedSlice n),
      (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up q) =
        ampleCyclicClassesPullback g n c → g ≫ d = q ≫ v := by
  obtain ⟨d, hd, hu⟩ := cyclicModuliInvariant_cover_descent n v hv c C p hp
  refine ⟨d, fun T g q hq ↦
    cyclicModuliInvariant_descent_evaluation n v hv c C p hp d hd g q hq, ?_⟩
  intro e he
  exact hu e (fun i ↦ he (C.X i) (C.f i) (p i) (hp i))

end FLT.Mazur.UniversalWeierstrass
