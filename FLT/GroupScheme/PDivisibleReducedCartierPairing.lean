/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierReducedNaturality
public import FLT.GroupScheme.PDivisibleCartierDlogLimit
public import FLT.GroupScheme.PDivisibleInfinitesimalPairing

/-! # Original dual Tate characters on infinitesimal points without a coefficient section -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
open HopfAlgebra.CartierDual
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)
  (q : B →ₐ[R] C) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
  (c : integralClosure R (AlgebraicClosure K) →ₐ[R] C)

local instance levelFree (n : ℕ) : Module.Free R (X.level n).CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- The original dual Tate character acts on finite infinitesimal points by its differential. -/
def reducedCartierAt (n : ℕ) (y : X.CartierTate) (f : X.LevelInfinitesimalKernel q n) : B :=
  reducedLogDifferential q hq (c.comp (X.cartierTateIntegralCoordinate n y))
    (AlgHom.augmentationPointToTangent _ q hJ f)

/-- The value belongs to the actual square-zero coefficient kernel. -/
theorem reducedCartierAt_mem_kernel (n : ℕ) (y : X.CartierTate)
    (f : X.LevelInfinitesimalKernel q n) : X.reducedCartierAt q hq hJ c n y f ∈ RingHom.ker q :=
  reducedLogDifferential_mem_kernel q hq _ _

/-- Every original inclusion preserves the reduced Cartier evaluation. -/
theorem reducedCartierAt_inclusion {m n : ℕ} (h : m ≤ n) (y : X.CartierTate)
    (f : X.LevelInfinitesimalKernel q m) :
    X.reducedCartierAt q hq hJ c n y (X.infinitesimalInclusion q h f) =
      X.reducedCartierAt q hq hJ c m y f := by
  unfold reducedCartierAt
  have he : (c.comp (X.cartierTateIntegralCoordinate n y)).comp
      (HopfAlgebra.CartierDual.map (X.inclusion h)) =
        c.comp (X.cartierTateIntegralCoordinate m y) := by
    rw [AlgHom.comp_assoc, X.cartierTateIntegralCoordinate_transition]
  rw [← he]
  apply (reducedLogDifferential_precomp q hq hJ (X.inclusion h) _ _ _ ?_).symm
  ext a
  change (f.val ((X.inclusion h) a) - algebraMap R B (Coalgebra.counit a)) =
    f.val ((X.inclusion h) a) - algebraMap R B (Coalgebra.counit ((X.inclusion h) a))
  rw [CoalgHomClass.counit_comp_apply]

/-- Two representatives of the actual infinitesimal colimit have the same Cartier value. -/
theorem reducedCartierAt_eq_of_colimit_eq {m n : ℕ} (y : X.CartierTate)
    (f : X.LevelInfinitesimalKernel q m) (g : X.LevelInfinitesimalKernel q n)
    (he : X.infinitesimalColimitMk q m f = X.infinitesimalColimitMk q n g) :
    X.reducedCartierAt q hq hJ c m y f = X.reducedCartierAt q hq hJ c n y g := by
  obtain ⟨k, hm, hn, hk⟩ := (X.pointColimitMk_eq_iff f.val g.val).mp (congrArg Subtype.val he)
  have hk' : X.infinitesimalInclusion q hm f = X.infinitesimalInclusion q hn g :=
    Subtype.ext hk
  rw [← X.reducedCartierAt_inclusion q hq hJ c hm,
    ← X.reducedCartierAt_inclusion q hq hJ c hn, hk']

/-- The original dual Tate character evaluates on the actual infinitesimal colimit. -/
def reducedCartierPairing (r : ℕ) (hr : ∀ b : RingHom.ker q, p ^ r • b = 0)
    (y : X.CartierTate) (z : X.InfinitesimalColimit q) : RingHom.ker q :=
  ⟨X.reducedCartierAt q hq hJ c r y ((X.infinitesimalColimitEquiv q hJ r hr).symm z),
    X.reducedCartierAt_mem_kernel q hq hJ c r y _⟩

/-- Every finite representative computes the same original pairing, regardless of the bound r. -/
theorem reducedCartierPairing_mk (r : ℕ) (hr : ∀ b : RingHom.ker q, p ^ r • b = 0)
    (n : ℕ) (y : X.CartierTate) (f : X.LevelInfinitesimalKernel q n) :
    (X.reducedCartierPairing q hq hJ c r hr y (X.infinitesimalColimitMk q n f) : B) =
      X.reducedCartierAt q hq hJ c n y f := by
  apply X.reducedCartierAt_eq_of_colimit_eq q hq hJ c
  exact (X.infinitesimalColimitEquiv q hJ r hr).apply_symm_apply _

end ThreeAdicPlan.PDivisibleSystem
