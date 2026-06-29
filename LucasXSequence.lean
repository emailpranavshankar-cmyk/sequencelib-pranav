import Mathlib
import Sequencelib.Meta
namespace Sequence
open Int

def KacMoodyX : ℕ × ℤ → ℤ
| (0, _) => 0
| (1, _) => 1
| (n + 2, k) => k * KacMoodyX (n+1, k) - KacMoodyX (n, k)

def KacMoodyY : ℕ × ℤ → ℤ
| (0, _) => 1
| (1, k) => k + 1
| (n + 2, k) => k * KacMoodyY (n+1, k) - KacMoodyY (n, k)

#eval KacMoodyY (3, 3)

theorem X_to_Y (n : ℕ) (k : ℤ) : KacMoodyY (n, k) = KacMoodyX (n, k) + KacMoodyX (n + 1, k) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyX, KacMoodyY]
  · simp [KacMoodyX, KacMoodyY]
    omega
  · have ih1 := ih n (by omega)
    have ih2 := ih (n + 1) (by omega)
    rw [show (n + 2) = n + 1 + 1 from by omega]
    have y_recursion : KacMoodyY (n+1+1, k) = k * KacMoodyY (n+1, k) - KacMoodyY (n, k) := by
      simp [KacMoodyY]
    rw [y_recursion, ih2, ih1]
    have firstx_recur : KacMoodyX (n+1+1, k) = k * KacMoodyX (n+1, k) - KacMoodyX (n, k) := by
      simp [KacMoodyX]
    have secondx_recur : KacMoodyX (n+1+1+1, k) = k * KacMoodyX (n+1+1, k) - KacMoodyX (n+1, k) := by
      simp [KacMoodyX]
    linarith
