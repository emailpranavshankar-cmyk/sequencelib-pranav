import Mathlib
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Complex.Basic
open Int
open Polynomial
open scoped NumberField

def KacMoodyX : ℕ × ℤ → ℤ
| (0, _) => 0
| (1, _) => 1
| (n + 2, k) => k * KacMoodyX (n+1, k) - KacMoodyX (n, k)


def KacMoodyY : ℕ × ℤ → ℤ
| (0, _) => 1
| (1, k) => k + 1
| (n + 2, k) => k * KacMoodyY (n+1, k) - KacMoodyY (n, k)

def KacMoodyX1Binary : ℕ × ℤ × ℤ → ℤ
| (0, _, _) => 1
| (1, a, b)=> a*b-1
| (n+2, a, b) => (a*b-2) * KacMoodyX1Binary (n+1, a, b) - KacMoodyX1Binary (n, a, b)
def KacMoodyX2Binary : ℕ × ℤ × ℤ → ℤ
| (0, _, _) => 0
| (1, a, _)=> a
| (n+2, a, b) => (a*b-2) * KacMoodyX2Binary (n+1, a, b) - KacMoodyX2Binary (n, a, b)
theorem X1Symm  (n : ℕ) (a: ℤ) (b: ℤ) : KacMoodyX1Binary (n, a, b) = KacMoodyX1Binary (n, b, a) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyX1Binary]
  · simp [KacMoodyX1Binary]
    ring
  · have ih1 := ih n (by omega)
    have ih2 := ih (n+1) (by omega)
    simp [KacMoodyX1Binary]
    rw [ih1, ih2]
    ring
theorem X2FirstArgumentMultiplication (n : ℕ) (a: ℤ) (b: ℤ) : KacMoodyX2Binary (n, a, b) = a * KacMoodyX2Binary (n, 1, a*b) := by
   induction n using Nat.strong_induction_on
   next n ih =>
   rcases n with _ | _ | n
   · simp [KacMoodyX2Binary]
   · simp [KacMoodyX2Binary]
   · have ih1 := ih n (by omega)
     have ih2 := ih (n+1) (by omega)
     simp [KacMoodyX2Binary]
     rw [ih1, ih2]
     ring

lemma KacMoodyX_skip_two (n : ℕ) (a : ℤ) :
    KacMoodyX (n + 4, a)
      = (a^2 - 2) * KacMoodyX (n + 2, a) - KacMoodyX (n, a) := by
  rw [show n + 4 = (n + 2) + 2 from rfl, KacMoodyX,
      show n+2+1 = (n+1)+2 from rfl, KacMoodyX, KacMoodyX]
  ring




theorem X_Even (n : ℕ) (a : ℤ) :
    KacMoodyX (2 * n, a) = KacMoodyX2Binary (n, a, a) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyX, KacMoodyX2Binary]
  · simp [KacMoodyX, KacMoodyX2Binary]
  · have ih1 := ih n (by omega)
    have ih2 := ih (n+1) (by omega)
    rw[show 2*(n+2) = 2*n+4 by ring]
    simp[KacMoodyX_skip_two]
    rw[KacMoodyX2Binary, show a*a-2 = a^2-2 by ring]
    rw[←ih1, ←ih2]
    rw[show 2*(n+1)= 2*n+2 by ring]










theorem X_Odd (n : ℕ) (a : ℤ) :
    KacMoodyX (2 * n + 1, a) = KacMoodyX1Binary (n, a, a) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyX, KacMoodyX1Binary]
  · simp [KacMoodyX, KacMoodyX1Binary]
  · have ih1 := ih n (by linarith)
    have ih2 := ih (n+1) (by linarith)
    rw[show 2*(n+2)+1 = (2*n+1)+4 by ring_nf]
    simp[KacMoodyX_skip_two]
    rw[KacMoodyX1Binary, show a*a-2 = a^2-2 by ring]
    rw[← ih1, ← ih2]
    rfl

theorem X2FromX (n : ℕ) (a : ℤ)(b: ℤ) : KacMoodyX2Binary (n, a, b) = a *KacMoodyX (n, a*b-2) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyX2Binary, KacMoodyX]
  · simp [KacMoodyX2Binary, KacMoodyX]
  · have ih1 := ih n (by omega)
    have ih2 := ih (n+1) (by omega)
    simp [KacMoodyX2Binary, KacMoodyX]
    rw [ih1,ih2]
    ring


theorem X_to_Y (n : ℕ) (k : ℤ) : KacMoodyY (n, k) = KacMoodyX (n, k) + KacMoodyX (n + 1, k) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyX, KacMoodyY]
  · simp [KacMoodyX, KacMoodyY]
    ring
  · have ih1 := ih n (by omega)
    have ih2 := ih (n + 1) (by omega)
    rw [show (n + 2) = n + 1 + 1 from by linarith]
    have y_recursion : KacMoodyY (n+1+1, k) = k * KacMoodyY (n+1, k) - KacMoodyY (n, k) := by
      simp [KacMoodyY]
    rw [y_recursion, ih2, ih1]
    have firstx_recur : KacMoodyX (n+1+1, k) = k * KacMoodyX (n+1, k) - KacMoodyX (n, k) := by
      simp [KacMoodyX]
    have secondx_recur : KacMoodyX (n+1+1+1, k) = k * KacMoodyX (n+1+1, k) - KacMoodyX (n+1, k) := by
      simp [KacMoodyX]
    linarith

theorem X1FromX (n : ℕ) (a : ℤ)(b: ℤ) : KacMoodyX1Binary (n, a, b) = KacMoodyX (n, a*b-2) + KacMoodyX (n+1, a*b-2):= by
  have ThruY (n : ℕ) (a : ℤ) (b : ℤ) : KacMoodyX1Binary (n, a, b) = KacMoodyY (n, a*b-2) := by
    induction n using Nat.strong_induction_on
    next n ih =>
    rcases n with _ | _ | n
    · simp [KacMoodyX1Binary, KacMoodyY]
    · simp [KacMoodyX1Binary, KacMoodyY]
      ring
    · have ih1 := ih n (by omega)
      have ih2 := ih (n+1) (by omega)
      simp [KacMoodyX1Binary, KacMoodyY]
      rw [ih1, ih2]
  rw [ThruY]
  rw [X_to_Y]

noncomputable def w1 (k : ℤ) : ℂ := ((k : ℂ) + Complex.sqrt ((k : ℂ)^2 - 4)) / 2
noncomputable def w2 (k : ℤ) : ℂ := ((k : ℂ) - Complex.sqrt ((k : ℂ)^2 - 4)) / 2


variable {F : Type*} [Field F] [NeZero (2 : F)]

lemma h_diff_field {F : Type*} [Field F] [CharNETwo : NeZero (2 : F)]
  (k : ℤ) (κ w1 w2 : F)
  (hκ : κ^2 = (k : F)^2 - 4)
  (hw1 : w1 = ((k : F) + κ) / 2)
  (hw2 : w2 = ((k : F) - κ) / 2)
  (hk2 : (k : F) ≠ 2 ∧ (k : F) ≠ -2) : w1 - w2 ≠ 0 := by
  have two_ne_zero : (2 : F) ≠ 0 := NeZero.ne 2
  intro h
  -- Step 1: w1 - w2 = κ
  have h_kappa : κ = 0 := by
    have heq : w1 - w2 = κ := by
      rw [hw1, hw2]
      field_simp
      ring
    rw [← heq]
    exact h
  -- Step 2: κ = 0 implies κ^2 = 0
  have h_sq_zero : κ^2 = 0 := by rw [h_kappa]; ring
  -- Step 3: So (k:F)^2 - 4 = 0
  rw [hκ] at h_sq_zero
  -- Step 4: Factor
  have h_factor : ((k : F) - 2) * ((k : F) + 2) = 0 := by
    linear_combination h_sq_zero
  rcases mul_eq_zero.mp h_factor with h1 | h2
  · exact hk2.1 (sub_eq_zero.mp h1)
  · exact hk2.2 (by rwa [add_eq_zero_iff_eq_neg] at h2)


def KacMoodyXRecGen (k : ℤ) : LinearRecurrence F where
  order := 2
  coeffs := ![-1, (k : F)]

lemma XExplicitFormulaGen (k : ℤ) (w1 w2 : F)
    (hw1 : w1^2 - (k : F) * w1 + 1 = 0)
    (hw2 : w2^2 - (k : F) * w2 + 1 = 0)
    (h_diff_F : w1 - w2 ≠ 0) :
    (fun n => (KacMoodyX (n, k) : F)) = fun n => (w1^n - w2^n) / (w1-w2) := by
  apply (LinearRecurrence.sol_eq_of_eq_init (KacMoodyXRecGen k) _ _ ?_ ?_).mpr
  · intro i hi
    norm_cast at hi
    fin_cases hi
    · simp [KacMoodyX]
    · simp [KacMoodyX]
      rw [div_self h_diff_F]


  · simp [LinearRecurrence.IsSolution, KacMoodyXRecGen]
    intro n
    simp [KacMoodyX]
    ring
  · simp [LinearRecurrence.IsSolution, KacMoodyXRecGen]
    intro n
    calc
      (w1 ^ (n + 2) - w2 ^ (n + 2)) / (w1 - w2) =
        (w1 ^ (n + 2) - w2 ^ (n + 2) - w1 ^ n * (w1 ^ 2 - (k : F) * w1 + 1) + w2 ^ n * (w2 ^ 2 - (k : F) * w2 + 1)) / (w1 - w2) := by
        rw [hw1, hw2]
        ring
      _ = (w2 ^ n - w1 ^ n + (k : F) * (w1 ^ (n + 1) - w2 ^ (n + 1))) / (w1 - w2) := by
        simp only [pow_add, pow_one]
        ring
      _ = -((w1 ^ n - w2 ^ n) / (w1 - w2)) + (k : F) * ((w1 ^ (n + 1) - w2 ^ (n + 1)) / (w1 - w2)) := by
        ring


lemma YExplicitFormulaRingSafe {R : Type*} [CommRing R] (k : ℤ) (w1 w2 : R)
  (hw1 : w1^2 - (k : R) * w1 + 1 = 0)
  (hw2 : w2^2 - (k : R) * w2 + 1 = 0) (n : ℕ) :
  (w1 - w2) * (KacMoodyY (n, k) : R) = w1^n * (w1 + 1) - w2^n * (w2 + 1) := by
  induction n using Nat.strong_induction_on
  next n ih =>
  rcases n with _ | _ | n
  · simp [KacMoodyY]
  · simp [KacMoodyY]
    grind
  · have ih1 := ih n (by grind)
    have ih2 := ih (n+1) (by grind)
    rw [KacMoodyY]
    have cast_out : (↑(k * KacMoodyY (n + 1, k) - KacMoodyY (n, k)) : R) =
    (k : R) * ↑(KacMoodyY (n + 1, k)) - ↑(KacMoodyY (n, k)) := by push_cast; rfl
    rw[cast_out]
    have distribute : (w1 - w2) * (↑k * ↑(KacMoodyY (n + 1, k)) - ↑(KacMoodyY (n, k))) =
    ↑k * ((w1 - w2) * ↑(KacMoodyY (n + 1, k))) - ((w1 - w2) * ↑(KacMoodyY (n, k))) := by ring
    rw [distribute, ih1, ih2]
    linear_combination - (w1^n * (w1 + 1)) * hw1 + (w2^n * (w2 + 1)) * hw2

noncomputable def P (p : ℕ) (k : ℤ) [Fact (Nat.Prime p)] : Polynomial (ZMod p) :=
  Polynomial.X ^ 2 - Polynomial.C (k : ZMod p) * Polynomial.X + 1

noncomputable def Fpw (p : ℕ) (k : ℤ) [Fact (Nat.Prime p)] : Type _ :=
  (P p k).SplittingField

noncomputable instance (p : ℕ) (k : ℤ) [Fact (Nat.Prime p)] : Field (Fpw p k) :=
  show Field (P p k).SplittingField from inferInstance

noncomputable instance (p : ℕ) (k : ℤ) [Fact (Nat.Prime p)] : Algebra (ZMod p) (Fpw p k) :=
  show Algebra (ZMod p) (P p k).SplittingField from inferInstance

noncomputable instance (p : ℕ) (k : ℤ) [Fact (Nat.Prime p)] : CharP (Fpw p k) p :=
  show CharP (P p k).SplittingField p from inferInstance

noncomputable def frob_alg (p : ℕ) (k : ℤ) [Fact (Nat.Prime p)] :
    Fpw p k →ₐ[ZMod p] Fpw p k :=
  AlgHom.mk' (frobenius (Fpw p k) p) (by
    intro r x
    simp only [_root_.frobenius_def, _root_.smul_pow, ZMod.pow_card])


lemma nonres_two_roots_exist_split_field (k : ℤ) (p : ℕ)
    [Fact (Nat.Prime p)] (h_nonres : ¬ IsSquare ((k ^ 2 - 4 : ℤ) : ZMod p)) :
    let P_local := P p k;
    ∃ w1 w2 : Fpw p k,
    w1 ≠ w2 ∧
      w1 ^ 2 - (k : Fpw p k) * w1 + 1 = 0 ∧
      w2 ^ 2 - (k : Fpw p k) * w2 + 1 = 0 ∧
      w1 * w2 = 1 ∧
      w1 + w2 = (k : Fpw p k) := by
  intro P_local
  have : Polynomial.Splits (P_local.map (algebraMap (ZMod p) (Fpw p k))) := by
    unfold P_local P Fpw
    apply Polynomial.SplittingField.splits
  have degree_eq_two : P_local.degree = 2 := by
    unfold P_local P
    compute_degree
    · simp
    · exact Nat.le_of_ble_eq_true rfl
    · exact Nat.le_of_ble_eq_true rfl
  obtain ⟨ w1, h ⟩ := Polynomial.Splits.exists_eval_eq_zero this (by
    simp
    rw [degree_eq_two]
    simp
  )
  unfold P_local P at h
  simp [Polynomial.aeval_def] at h
  have : ∃ w2 : Fpw p k, w2 * w2 - ↑k * w2 + 1 = 0 ∧ w1 + w2 = ↑k ∧ w1 * w2 = 1 := by
    apply vieta_formula_quadratic
    unfold P_local P at *
    simp at *
    grind
  obtain ⟨ w2, he, hs, hp ⟩ := this
  use w1, w2
  simp at *
  have p_ne_two : p ≠ 2 := by
    intro pt
    have x : (k : (ZMod 2)) ^ 2 - 4 = k ^ 2 := by grind
    subst p
    rw [x] at h_nonres
    exact h_nonres (IsSquare.sq _)
  exact ⟨
    by
      intro hw1
      have a : w1^2 = 1 := by
        rw [← hw1] at hp
        ring_nf at hp
        exact hp
      have b : w1 * 2 = k := by
        rw[← hw1] at hs
        linear_combination hs
      rw [a] at h
      ring_nf at h
      apply_fun (fun x => x * (-2) + 4) at h
      ring_nf at h
      conv at h =>
        lhs
        rw [mul_assoc]
      rw [b] at h
      ring_nf at h
      let K := Fpw p k
      have d : (k : K) ^ 2 - 4 = 0 := by
        subst K
        rw [h]
        simp
      norm_cast at d
      have e : (p : ℤ) ∣ (k ^ 2 - 4) := by
        refine (CharP.intCast_eq_zero_iff (Fpw p k) p ?_).mp ?_
        exact d
      have f : (k : ZMod p) ^ 2 - 4 = 0 := by
        norm_cast
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 2 - 4) p).mpr e
      rw [f] at h_nonres
      simp at h_nonres,
    h,
    by simp only [pow_two]; exact he,
    hp,
    hs
  ⟩

theorem PrimeDivisibilityX (k : ℤ) (p : ℕ) (hk : 0 < k) [Fact (Nat.Prime p)] :
  ∃ n : ℕ, n > 0 ∧ (p : ℤ) ∣ KacMoodyX (n, k) := by

  by_cases h_zero : ((k^2 - 4 : ℤ) : ZMod p) = 0

  · -- CASE 1: The Zero Case (k^2 - 4 = 0 mod p)
    have h_sq : (k : ZMod p)^2 = (2 : ZMod p)^2 := by
      calc (k : ZMod p)^2
        _ = ((k^2 - 4 : ℤ) : ZMod p) + (4 : ZMod p) := by push_cast; ring
        _ = 0 + (4 : ZMod p) := by rw [h_zero]
        _ = (2 : ZMod p)^2 := by ring

    have pm_two_mod_p : (k: ZMod p) = 2 ∨ (k : ZMod p) = -2 := sq_eq_sq_iff_eq_or_eq_neg.mp h_sq

    rcases pm_two_mod_p with kpos | kneg

    · -- Sub-case 1A: k = 2 mod p
      have arithmetic_seq : ∀ m : ℕ, (KacMoodyX (m, k) : ZMod p) = (m : ZMod p) := by
        intro m
        induction m using Nat.strong_induction_on
        next m ih =>
        rcases m with _ | _ | m
        · push_cast
          simp [KacMoodyX]
        · push_cast
          simp [KacMoodyX]
        · have ih1 := ih m (by push_cast; omega)
          have ih2 := ih (m + 1) (by push_cast; omega)
          simp [KacMoodyX]
          rw [ih1, ih2, kpos]
          push_cast
          ring

      use p
      constructor
      · exact Nat.Prime.pos Fact.out
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [arithmetic_seq p]
        simp

    · -- Sub-case 1B: k = -2 mod p
      have alt_arithmetic_seq : ∀ m : ℕ, (KacMoodyX (m, k) : ZMod p) = (m : ZMod p) * (-1 : ZMod p)^(m + 1) := by
        intro m
        induction m using Nat.strong_induction_on
        next m ih =>
        rcases m with _ | _ | m
        · push_cast
          simp [KacMoodyX]
        · push_cast
          simp [KacMoodyX]
        · have ih1 := ih m (by push_cast; omega)
          have ih2 := ih (m + 1) (by push_cast; omega)
          simp [KacMoodyX]
          rw [ih1, ih2, kneg]
          push_cast
          ring
      use p
      constructor
      · exact Nat.Prime.pos Fact.out
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [alt_arithmetic_seq p]
        simp

  · have h_res_or_nonres : legendreSym p (k^2 - 4) = 1 ∨ legendreSym p (k^2 - 4) = -1 :=
      legendreSym.eq_one_or_neg_one p h_zero

    rcases h_res_or_nonres with h_res | h_nonres
    · by_cases hp2 : p = 2
      · subst hp2
        by_cases hkeven : Even k
        · obtain ⟨m, hm⟩ := hkeven
          use 2
          constructor
          · linarith
          · simp [KacMoodyX, hm]
            ring_nf
            omega
        · rw [Int.not_even_iff_odd] at hkeven
          obtain ⟨m, hm⟩ := hkeven
          use 3
          constructor
          · omega
          · simp [KacMoodyX, hm]
            ring_nf
            omega


      · rw [legendreSym.eq_one_iff] at h_res
        any_goals exact h_zero
        use p-1
        constructor
        · exact Nat.Prime.pred_pos (Fact.out : Nat.Prime p)
        · obtain ⟨κ, hkappa⟩ := h_res
          have hkappa_sq : κ^2 = (k : ZMod p)^2 - 4 := by
            calc κ^2 = κ * κ := by ring
            _ = ((k^2 - 4 : ℤ) : ZMod p) := hkappa.symm
            _ = (k : ZMod p)^2 - 4 := by push_cast; ring
          let w1 : ZMod p := (k + κ) / 2
          let w2 : ZMod p := (k - κ) / 2
          have TwoNotZero : NeZero (2 : ZMod p) := by
            by_contra two_is_zero
            apply hp2
            have h2 : (2 : ZMod p) = 0 := by_contra (fun h => two_is_zero ⟨h⟩)
            have div2 : p ∣ 2 := by
              change ((2 : ℕ) : ZMod p) = 0 at h2
              exact (ZMod.natCast_eq_zero_iff 2 p).mp h2
            have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) div2
            have hp_ge : 2 ≤ p := Nat.Prime.two_le Fact.out
            omega

          have hw1 : w1^2 - (k : ZMod p) * w1 + 1 = 0 := by
             unfold w1
             field_simp
             ring_nf
             rw [hkappa_sq]
             ring
          have hw2 : w2^2 - (k : ZMod p) * w2 + 1 = 0 := by
             unfold w2
             field_simp
             ring_nf
             rw [hkappa_sq]
             ring
          have kNotTwo: (k : ZMod p) ≠ 2 ∧ (k : ZMod p) ≠ -2 := by
             constructor
             · intro two
               apply h_zero
               push_cast
               rw[two]
               ring
             · intro minus
               apply h_zero
               push_cast
               rw[minus]
               ring
          have h_diff : w1 - w2 ≠ 0 := h_diff_field k κ w1 w2 hkappa_sq rfl rfl kNotTwo
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          have h_explicit := congr_fun (XExplicitFormulaGen k w1 w2 hw1 hw2 h_diff) (p - 1)
          rw [h_explicit]
          rw [div_eq_zero_iff]
          apply Or.inl
          have prodOne : w1 * w2 = 1 := by
             unfold w1
             unfold w2
             ring_nf
             field_simp
             rw [hkappa_sq]
             ring
          have w1Nonzero : w1 ≠ 0 := by
            by_contra h
            have : (0 : ZMod p) = 1 := by
              calc
              0 = w1 * w2 := by simpa [h] using prodOne
              _ = 1 := prodOne
            exact zero_ne_one this
          have w2Nonzero : w2 ≠ 0 := by
            by_contra h
            have : (0 : ZMod p) = 1 := by
              calc
              0 = w1 * w2 := by simpa [h] using prodOne
              _ = 1 := prodOne
            exact zero_ne_one this
          rw [ZMod.pow_card_sub_one_eq_one w1Nonzero]
          rw [ZMod.pow_card_sub_one_eq_one w2Nonzero]
          ring_nf
    · rw [legendreSym.eq_neg_one_iff] at h_nonres
      use p+1
      constructor
      · have ppos : 0 < p := Nat.Prime.pos Fact.out
        omega
      · obtain ⟨w1, w2, props⟩ := nonres_two_roots_exist_split_field k p h_nonres
        have frob_lemma_one : Polynomial.aeval (w1 ^ p) (P p k) = 0 := by
           rw [show w1 ^ p = frob_alg p k w1 from by simp [frob_alg, frobenius_def]]
           rw [Polynomial.aeval_algHom_apply (frob_alg p k) w1 (P p k)]
           simp
           unfold P
           simp[props.2.1]
        have frob_lemma_two : Polynomial.aeval (w2 ^ p) (P p k) = 0 := by
           rw [show w2 ^ p = frob_alg p k w2 from by simp [frob_alg, frobenius_def]]
           rw [Polynomial.aeval_algHom_apply (frob_alg p k) w2 (P p k)]
           simp
           unfold P
           simp[props.2.2.1]
        have frob_lemma_three : w1 ^ p = w2 := by
          have its_w1_or_w2 : (w1 ^ p = w1) ∨ (w1 ^ p = w2) := by
             have factorization : (w1 ^ p - w1) * (w1 ^ p - w2) = 0 := by
                unfold P at frob_lemma_one
                simp [Polynomial.aeval_mul, Polynomial.aeval_sub,
                Polynomial.aeval_X, Polynomial.aeval_C] at frob_lemma_one
                have key : (w1 ^ p - w1) * (w1 ^ p - w2) =
             w1 ^ (p * 2) - w1 ^ p * (w1 + w2) + w1 * w2 := by ring
                rw [key, props.2.2.2.1, props.2.2.2.2]
                push_cast
                ring_nf
                ring_nf at frob_lemma_one
                exact frob_lemma_one
             rcases mul_eq_zero.mp factorization with left | right
             · left
               exact sub_eq_zero.mp left
             · right
               exact sub_eq_zero.mp right
          rcases its_w1_or_w2 with madness | method
          · exfalso
            have hw1_bot : w1 ∈ (⊥ : Subfield (Fpw p k)) :=
            (Subfield.mem_bot_iff_pow_eq_self (Fpw p k) p).mpr madness
            rw [mem_bot_iff_intCast p (Fpw p k)] at hw1_bot
            obtain ⟨w, wint⟩ := hw1_bot
            have hw1_root := props.2.1
            rw [← wint] at hw1_root
            have hzmod : (w : ZMod p)^2 - (k : ZMod p) * w + 1 = 0 := by
                apply (algebraMap (ZMod p) (Fpw p k)).injective
                simp [map_sub, map_add, map_pow, map_mul, map_one]
                push_cast
                exact hw1_root
            apply h_nonres
            use (2 * (w : ZMod p) - (k: ZMod p))
            push_cast
            ring_nf
            push_cast
            have kw : (k: ZMod p) * (w : ZMod p) = 1 + (w: ZMod p)^2 := by linear_combination -hzmod
            rw [kw]
            ring
          · exact method
        have frob_lemma_four : w2 ^ p = w1 := by
          have its_w1_or_w2 : (w2 ^ p = w2) ∨ (w2 ^ p = w1) := by
            have factorization : (w2 ^ p - w2) * (w2 ^ p - w1) = 0 := by
               unfold P at frob_lemma_two
               simp [Polynomial.aeval_mul, Polynomial.aeval_sub,
                    Polynomial.aeval_X, Polynomial.aeval_C] at frob_lemma_two
               have key : (w2 ^ p - w2) * (w2 ^ p - w1) =
                       w2 ^ (p * 2) - w2 ^ p * (w2 + w1) + w2 * w1 := by ring
               rw [key]
               rw [show w2 + w1 = w1 + w2 from by ring]
               rw [show w2 * w1 = w1 * w2 from by ring]
               rw [props.2.2.2.1, props.2.2.2.2]
               push_cast
               ring_nf
               ring_nf at frob_lemma_two
               exact frob_lemma_two
            rcases mul_eq_zero.mp factorization with left | right
            · left
              exact sub_eq_zero.mp left
            · right
              exact sub_eq_zero.mp right
          rcases its_w1_or_w2 with madnessfour | methodfour
          · exfalso
            have hw2_bot : w2 ∈ (⊥ : Subfield (Fpw p k)) :=
            (Subfield.mem_bot_iff_pow_eq_self (Fpw p k) p).mpr madnessfour
            rw [mem_bot_iff_intCast p (Fpw p k)] at hw2_bot
            obtain ⟨w, wintwo⟩ := hw2_bot
            have hw2_root := props.2.2.1
            rw [← wintwo] at hw2_root
            have hzmod : (w : ZMod p)^2 - (k : ZMod p) * w + 1 = 0 := by
                apply (algebraMap (ZMod p) (Fpw p k)).injective
                simp [map_sub, map_add, map_pow, map_mul, map_one]
                push_cast
                exact hw2_root
            apply h_nonres
            use (2 * (w : ZMod p) - (k: ZMod p))
            push_cast
            ring_nf
            push_cast
            have kw : (k: ZMod p) * (w : ZMod p) = 1 + (w: ZMod p)^2 := by linear_combination -hzmod
            rw [kw]
            ring
          · exact methodfour
        have roots_diff: w1 - w2 ≠ 0 := by
          intro no_diff
          have eq : w1 = w2 := by
            apply sub_eq_zero.mp no_diff
          absurd props.1 eq
          intro notfalse
          exact notfalse
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hp_ne_two : p ≠ 2 := by
          intro p_two
          subst p_two
          apply h_nonres
          use (k: ZMod 2)
          push_cast
          ring_nf
          simp
          rfl
        have char_not_two : NeZero (2: Fpw p k) := by
          by_contra two_is_zero_in_Fpw
          apply hp_ne_two
          rw [neZero_iff, ne_eq, not_not] at two_is_zero_in_Fpw
          have char_lemma := (CharP.cast_eq_zero_iff (Fpw p k) p 2).mp
          have p_div_two := char_lemma two_is_zero_in_Fpw
          have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) p_div_two
          have hp_ge : 2 ≤ p := Nat.Prime.two_le Fact.out
          omega







        have explicit := congr_fun (XExplicitFormulaGen k w1 w2 props.2.1 props.2.2.1 roots_diff) (p + 1)
        have zero_in_Fpw : ((KacMoodyX (p+1, k): Fpw p k) = 0) := by
          rw[explicit]
          ring_nf
          field_simp
          simp
          rw [frob_lemma_three, frob_lemma_four]
          ring
        have zero_in_ZMod : ((KacMoodyX (p+1, k) : ℤ) : ZMod p) = 0 := by
            apply (algebraMap (ZMod p) (Fpw p k)).injective
            simp only [map_zero, map_intCast]
            exact_mod_cast zero_in_Fpw
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (KacMoodyX (p+1, k)) p).mp zero_in_ZMod


variable (k : ℤ)
variable (p : ℕ) [Fact (Nat.Prime p)]

-- 2. Define K as a Number Field over ℚ
variable (K : Type*) [Field K] [NumberField K]

-- 3. Assert that K is specifically the splitting field of X^2 - kX + 1 over ℚ
-- We cast k to ℚ and use C to inject it into the polynomial ring ℚ[X]
variable [IsSplittingField ℚ K (X^2 - C (k : ℚ) * X + 1)]

-- 4. Set up the ideal generated by p in the ring of integers 𝓞 K
local notation "I_p" => Ideal.span {((p : ℤ) : 𝓞 K)}

-- 5. Define the quotient ring 𝓞_K / (p)
local notation "O_K_mod_p" => (𝓞 K) ⧸ I_p


theorem PrimeDivisibilityYIf
    (h1 : 0 < k)
    (pod : p ≠ 2)
    (α β : (O_K_mod_p)ˣ)
    (hroot1 : (α : O_K_mod_p) ^ 2 - (k : O_K_mod_p) * (α : O_K_mod_p) + 1 = 0)
    (hroot2 : (β : O_K_mod_p) ^ 2 - (k : O_K_mod_p) * (β : O_K_mod_p) + 1 = 0)
    (hodd : Odd (orderOf α))
    (not_minus_2 : (k : ZMod p) ≠ -2) :
    ∃ n : ℕ, n > 0 ∧ (p : ℤ) ∣ KacMoodyY (n, k) := by
         by_cases zero : ((k^2 - 4 : ℤ) : ZMod p) = 0
         · have h_sq : (k : ZMod p)^2 = (2 : ZMod p)^2 := by
            calc (k : ZMod p)^2
            _ = ((k^2 - 4 : ℤ) : ZMod p) + (4 : ZMod p) := by push_cast; ring
            _ = 0 + (4 : ZMod p) := by rw [zero]
            _ = (2 : ZMod p)^2 := by ring


           have pm_two_mod_p : (k: ZMod p) = 2 ∨ (k : ZMod p) = -2 := sq_eq_sq_iff_eq_or_eq_neg.mp h_sq
           rcases pm_two_mod_p with kpos | kneg
           · have arithmetic_seq : ∀ m : ℕ, (KacMoodyY (m, k) : ZMod p) = (2 * m + 1: ZMod p) := by
                intro m
                induction m using Nat.strong_induction_on
                next m ih =>
                rcases m with _ | _ | m
                · push_cast
                  simp [KacMoodyY]
                · ring_nf
                  push_cast
                  simp [KacMoodyY]
                  rw [kpos]
                  ring
                · have ih1 := ih m (by push_cast; omega)
                  have ih2 := ih (m + 1) (by push_cast; omega)
                  simp [KacMoodyY]
                  rw [ih1, ih2, kpos]
                  push_cast
                  ring
             use (p-1)/2
             constructor
             · have := (Fact.out : Nat.Prime p).two_le
               have := (Fact.out : Nat.Prime p).odd_of_ne_two pod
               omega
             · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
               rw [arithmetic_seq]
               have twos_cancellable : (2 * ((p - 1) / 2) + 1 : ℕ) = p := by
                  obtain ⟨m, hm⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two pod
                  omega
               norm_cast
               rw [twos_cancellable]
               rw [ZMod.natCast_self p]


           · exfalso
             contradiction





         · obtain ⟨ord, hord ⟩ := hodd

































theorem PrimeDivisibilityYOnlyIf (k : ℤ) (p : ℕ) (h1 : 0 < k) (h2 : Nat.Prime p) (α : (ZMod p)ˣ)
    (hroot : (α : ZMod p) ^ 2 - (k : ZMod p) * (α : ZMod p) + 1 = 0)
    (heven : Even (orderOf α)) :
    ∀ n : ℕ, n > 0 → ¬(p : ℤ) ∣ KacMoodyY (n, k) := by
