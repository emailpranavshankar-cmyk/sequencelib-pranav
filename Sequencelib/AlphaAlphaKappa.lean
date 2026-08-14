import Mathlib
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Complex.Basic
import Sequencelib.Meta
namespace Sequence
open Int
open Polynomial
open scoped NumberField
open Finset
open scoped BigOperators
lemma alpha_alpha_kappa (pod : p ≠ 2) (α β : (O_K_mod_p)ˣ) (hdiff : α ≠ β)
    (nontriv: NeZero 1)
    (κ : O_K_mod_p) (hκ : κ^2 = (k : O_K_mod_p)^2 - 4)
    (hroot1 : 2 * (α : O_K_mod_p) = (k : O_K_mod_p) + κ)
    (hroot2 : 2 * (β : O_K_mod_p) = (k : O_K_mod_p) - κ)
    (alpha_nonscalar : (α : O_K_mod_p) ∉ Set.range (algebraMap (ZMod p) (𝓞 K ⧸ Ideal.span {(p:𝓞 K)}))) :
    α ∈ kappa_p p K := by
         unfold kappa_p
         show (f p K) α = 1
         unfold f
         have old_hroot1 := old_hroot1_lemma k p K pod α β hdiff κ hκ hroot1 hroot2
         have basis_former : LinearIndependent (ZMod p) ![(1 : O_K_mod_p), (α : O_K_mod_p)] := by
           rw [LinearIndependent.pair_iff]
           intro s t hst
           have snull : s = 0 := by
             by_contra
             apply alpha_nonscalar
             have no_cancel: t ≠ 0 := by
                by_contra cancel
                rw [cancel] at hst
                simp at hst
                rcases hst with left | right
                · contradiction
                · haveI : Nontrivial (𝓞 K ⧸ Ideal.span {(p:𝓞 K)}) := by
                    have hprime : Fact (Nat.Prime p) := inferInstance
                    exact CharP.nontrivial_of_char_ne_one hprime.out.one_lt.ne'
                  exact one_ne_zero right
             use -s/t
             have ha_eq : (t : ZMod p) • (α : O_K_mod_p) = (-s) • (1 : O_K_mod_p) := by
                simp [hst]
                linear_combination hst
             have ha : (α : O_K_mod_p) = algebraMap (ZMod p) O_K_mod_p (-s / t) := by
                have ht_unit : IsUnit t := Ne.isUnit no_cancel
                have hinv : algebraMap (ZMod p) O_K_mod_p t⁻¹ * algebraMap (ZMod p) O_K_mod_p t = 1 := by rw [← map_mul, inv_mul_cancel₀ no_cancel, map_one]
                rw [Algebra.smul_def] at ha_eq
                simp only [Algebra.smul_def] at ha_eq
                simp at ha_eq
                rw [div_eq_mul_inv, map_mul, map_neg]
                linear_combination (algebraMap (ZMod p) O_K_mod_p t⁻¹) * ha_eq - (α : O_K_mod_p) * hinv
             rw[ha]
           have tnull : t = 0 := by
             rw [snull] at hst; simp at hst
             rcases hst with left | right
             · exact left
             · exfalso
               rw [right] at old_hroot1
               simp at old_hroot1
               haveI : Nontrivial (𝓞 K ⧸ Ideal.span {(p:𝓞 K)}) := by
                    have hprime : Fact (Nat.Prime p) := inferInstance
                    exact CharP.nontrivial_of_char_ne_one hprime.out.one_lt.ne'
               exact one_ne_zero old_hroot1
           constructor
           · exact snull
           · exact tnull
         have spans : Submodule.span (ZMod p) ({(1 : O_K_mod_p), (α : O_K_mod_p)} : Set O_K_mod_p) = ⊤ := by
           obtain ⟨w, hw_lift⟩ : ∃ w : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) w = (α : O_K_mod_p) := sorry
           have hw_root : w ^ 2 - (k : 𝓞 K) * w + 1 = 0 := sorry
           have field_up : K = Algebra.adjoin ℚ ({(w : K)} : Set K) := by sorry
           have ring_int : 𝓞 K = Algebra.adjoin ℤ ({w} : Set (𝓞 K)) := by sorry
         sorry
