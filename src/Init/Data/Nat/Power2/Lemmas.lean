/-
Copyright (c) George Rennie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Rennie
-/
module

prelude
import all Init.Data.Nat.Power2.Basic
public import Init.Data.Nat.Log2
public import Init.Data.Nat.Power2.Basic
public import Init.PropLemmas
import Init.ByCases
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Omega
import Init.RCases

public section

/-!
# Further lemmas about `Nat.isPowerOfTwo`, with the convenience of having bitwise lemmas available.
-/

namespace Nat

theorem not_isPowerOfTwo_zero : ¬isPowerOfTwo 0 := by
  rw [isPowerOfTwo, not_exists]
  intro x
  have := one_le_pow x 2 (by decide)
  omega

theorem and_sub_one_testBit_log2 {n : Nat} (h : n ≠ 0) (hpow2 : ¬n.isPowerOfTwo) :
    (n &&& (n - 1)).testBit n.log2 := by
  rw [testBit_and, Bool.and_eq_true]
  constructor
  · exact testBit_log2 (by omega)
  · by_cases n = 2^n.log2
    · rw [isPowerOfTwo, not_exists] at hpow2
      have := hpow2 n.log2
      trivial
    · have := log2_eq_iff (n := n) (k := n.log2) (by omega)
      have : (n - 1).log2 = n.log2 := by rw [log2_eq_iff] <;> omega
      rw [←this]
      exact testBit_log2 (by omega)

theorem and_sub_one_eq_zero_iff_isPowerOfTwo {n : Nat} (h : n ≠ 0) :
    (n &&& (n - 1)) = 0 ↔ n.isPowerOfTwo := by
  constructor
  · intro hbitwise
    false_or_by_contra
    rename_i hpow2
    have := and_sub_one_testBit_log2 h hpow2
    rwa [hbitwise, zero_testBit n.log2, Bool.false_eq_true] at this
  · intro hpow2
    rcases hpow2 with ⟨_, hpow2⟩
    rw [hpow2, and_two_pow_sub_one_eq_mod, mod_self]

theorem ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo {n : Nat} :
    ((n ≠ 0) ∧ (n &&& (n - 1)) = 0) ↔ n.isPowerOfTwo := by
  match h : n with
  | 0 => simp [not_isPowerOfTwo_zero]
  | n + 1 => simp; exact and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)

@[inline]
instance {n : Nat} : Decidable n.isPowerOfTwo :=
  decidable_of_iff _ ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo

theorem le_nextPowerOfTwo (n : Nat) : n ≤ n.nextPowerOfTwo :=
  le_go 1 (by decide)
where
  le_go (power : Nat) (h : power > 0) : n ≤ nextPowerOfTwo.go n power h := by
    unfold nextPowerOfTwo.go
    split
    · exact le_go (power * 2) (Nat.mul_pos h (by decide))
    · omega
  termination_by n - power
  decreasing_by simp_wf; apply nextPowerOfTwo_dec <;> assumption

theorem nextPowerOfTwo_le {n m : Nat} (hm : m.isPowerOfTwo) (hn : n ≤ m) :
    n.nextPowerOfTwo ≤ m :=
  go_le 1 (by decide) isPowerOfTwo_one (pos_of_isPowerOfTwo hm) hm hn
where
  go_le (power : Nat) (h₁ : power > 0) (h₂ : power.isPowerOfTwo) (hpm : power ≤ m)
      (hm : m.isPowerOfTwo) (hn : n ≤ m) : nextPowerOfTwo.go n power h₁ ≤ m := by
    unfold nextPowerOfTwo.go
    split
    · rename_i hlt
      apply go_le (power * 2) (Nat.mul_pos h₁ (by decide))
        (isPowerOfTwo_mul_two_of_isPowerOfTwo h₂) _ hm hn
      obtain ⟨k, rfl⟩ := h₂
      obtain ⟨j, rfl⟩ := hm
      rw [← Nat.pow_succ]
      exact Nat.pow_le_pow_right (by decide)
        ((Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_lt_of_le hlt hn))
    · assumption
  termination_by n - power
  decreasing_by simp_wf; apply nextPowerOfTwo_dec <;> assumption

theorem nextPowerOfTwo_eq_self {n : Nat} (h : n.isPowerOfTwo) : n.nextPowerOfTwo = n :=
  Nat.le_antisymm (nextPowerOfTwo_le h (Nat.le_refl n)) (le_nextPowerOfTwo n)

lemma nextPowerOfTwo_eq_two_pow_clog (n : ℕ) : n.nextPowerOfTwo = 2 ^ Nat.clog 2 n := by
  have hle := nextPow2_nat_ge n
  obtain ⟨k, hk⟩ := Nat.isPowerOfTwo_nextPowerOfTwo n
  rw [hk]
  simp_all only [Order.lt_two_iff, zero_le, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
    pow_right_inj₀]
  apply_fun Nat.clog 2 at hle using Nat.clog_monotone 2
  have clogpow (k : ℕ) : Nat.clog 2 (2 ^ k) = k := by
    simp_all only [Order.lt_two_iff, le_refl, Nat.clog_pow]
  rw [clogpow] at hle
  suffices k ≤ Nat.clog 2 n by linarith
  have : n.nextPowerOfTwo ≤ 2 ^ Nat.clog 2 n :=
    (nextPow2_nat_le n <| Nat.clog 2 n) <| Nat.le_pow_clog (by decide) n
  rw [hk] at this
  apply_fun Nat.clog 2 at this using Nat.clog_monotone 2
  simpa [clogpow] using this

end Nat
