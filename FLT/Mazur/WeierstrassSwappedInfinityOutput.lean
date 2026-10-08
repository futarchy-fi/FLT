/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedInfinitySlopes

/-!
# Normalized infinity addition on reversed inputs

Equality of homogeneous outputs identifies their normalizing inverses. Thus the
actual infinity addition algebra maps agree on every reversed-input intersection.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f g : InfinityAdditionOpen W →ₐ[R] S)
  (hbase : g.comp (infinityAdditionRestriction W) =
    (f.comp (infinityAdditionRestriction W)).comp (chartProductSwap W 1 1))

include hbase

/-- The restricted homogeneous outputs coincide with reversed inputs. -/
theorem infinityRestrictedOutput_swap (i : Fin 3) :
    f (infinityOutputRestriction W (infinityOutputCoordinates W i)) =
      g (infinityOutputRestriction W (infinityOutputCoordinates W i)) :=
  infinityOutputCoordinates_swap W (f.comp (infinityOutputRestriction W))
    (g.comp (infinityOutputRestriction W)) hbase i

/-- The infinity output normalization is preserved under input reversal. -/
theorem infinityOutputInverse_swap :
    f (infinityOutputInverse W) = g (infinityOutputInverse W) := by
  have hf := congrArg f (infinityOutputInverse_mul W)
  have hg := congrArg g (infinityOutputInverse_mul W)
  simp only [map_mul, map_one] at hf hg
  rw [← infinityRestrictedOutput_swap W f g hbase 1] at hg
  calc
    f (infinityOutputInverse W) = f (infinityOutputInverse W) *
        (g (infinityOutputInverse W) *
          f (infinityOutputRestriction W (infinityOutputCoordinates W 1))) := by
      rw [hg, mul_one]
    _ = g (infinityOutputInverse W) := by rw [mul_left_comm, hf, mul_one]

/-- The normalized infinity-chart addition maps agree on reversed-input domains. -/
theorem infinityAdditionChart_swap :
    f.comp (infinityAdditionChart W) = g.comp (infinityAdditionChart W) := by
  apply hom_ext
  intro i
  change f (infinityAdditionChart W (coord W 1 i)) =
    g (infinityAdditionChart W (coord W 1 i))
  rw [infinityAdditionChart_coord, map_mul, map_mul,
    infinityOutputInverse_swap W f g hbase, infinityRestrictedOutput_swap W f g hbase]

end FLT.Mazur.WeierstrassIntegralChart
