set_option Elab.async false
-- Syracuse map: for odd x, syr x is the odd part of 3x + 1. Halving uses explicit fuel so the kernel can evaluate it.
def oddpartF : Nat → Nat → Nat | 0, n => n | f + 1, n => if n % 2 = 0 ∧ 0 < n then oddpartF f (n / 2) else n
def vF : Nat → Nat → Nat | 0, _ => 0 | f + 1, n => if n % 2 = 0 ∧ 0 < n then vF f (n / 2) + 1 else 0
theorem oddpart_spec (f : Nat) : ∀ n : Nat, 0 < n → n ≤ 2 ^ f →
    2 ^ vF f n * oddpartF f n = n ∧ oddpartF f n % 2 = 1 := by
  induction f with
  | zero => intro n h0 h1; simp [vF, oddpartF] at *; omega
  | succ f ih =>
    intro n h0 h1
    by_cases h : n % 2 = 0 ∧ 0 < n
    · have hn2 : 0 < n / 2 := by omega
      have hn3 : n / 2 ≤ 2 ^ f := by rw [Nat.pow_succ] at h1; omega
      obtain ⟨e1, e2⟩ := ih (n / 2) hn2 hn3
      simp only [vF, oddpartF, h, and_self, ite_true]
      refine ⟨?_, e2⟩
      rw [Nat.pow_succ]
      have : 2 ^ vF f (n / 2) * 2 * oddpartF f (n / 2) = 2 * (2 ^ vF f (n / 2) * oddpartF f (n / 2)) := by grind
      rw [this, e1]; omega
    · simp only [vF, oddpartF, h, ite_false]
      constructor
      · simp
      · omega
def syr (x : Nat) : Nat := oddpartF (3 * x + 1) (3 * x + 1)
def v (x : Nat) : Nat := vF (3 * x + 1) (3 * x + 1)
theorem syr_spec (x : Nat) (hx : x % 2 = 1) : 2 ^ v x * syr x = 3 * x + 1 ∧ syr x % 2 = 1 ∧ 1 ≤ v x := by
  have hle : 3 * x + 1 ≤ 2 ^ (3 * x + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  obtain ⟨e1, e2⟩ := oddpart_spec (3 * x + 1) (3 * x + 1) (by omega) hle
  refine ⟨e1, e2, ?_⟩
  unfold v
  by_cases hv : vF (3 * x + 1) (3 * x + 1) = 0
  · rw [hv] at e1; simp at e1; rw [e1] at e2; omega
  · omega
def iterS : Nat → Nat → Nat | 0, x => x | k + 1, x => iterS k (syr x)
def P : Nat → Nat → Nat | 0, _ => 1 | k + 1, x => (3 * x + 1) * P k (syr x)
def R : Nat → Nat → Nat | 0, _ => 1 | k + 1, x => x * R k (syr x)
def Q : Nat → Nat → Nat | 0, _ => 1 | k + 1, x => syr x * Q k (syr x)
def V : Nat → Nat → Nat | 0, _ => 0 | k + 1, x => v x + V k (syr x)
theorem iterS_odd (k : Nat) : ∀ x : Nat, x % 2 = 1 → iterS k x % 2 = 1 := by
  induction k with
  | zero => intro x hx; exact hx
  | succ k ih => intro x hx; exact ih (syr x) (syr_spec x hx).2.1
theorem iterS_add (a : Nat) : ∀ b x : Nat, iterS (a + b) x = iterS a (iterS b x) := by
  induction a with
  | zero => intro b x; simp [iterS]
  | succ a ih =>
    intro b x
    induction b generalizing x with
    | zero => simp [iterS]
    | succ b ihb =>
      show iterS (a + 1 + b) (syr x) = iterS (a + 1) (iterS b (syr x))
      exact ihb (syr x)
theorem prodV (k : Nat) : ∀ x : Nat, x % 2 = 1 → 2 ^ V k x * Q k x = P k x := by
  induction k with
  | zero => intro x _; simp [V, Q, P]
  | succ k ih =>
    intro x hx
    obtain ⟨e1, e2, _⟩ := syr_spec x hx
    have h := ih (syr x) e2
    show 2 ^ (v x + V k (syr x)) * (syr x * Q k (syr x)) = (3 * x + 1) * P k (syr x)
    rw [← e1, ← h, Nat.pow_add]; grind
theorem QR (k : Nat) : ∀ x : Nat, Q k x * x = R k x * iterS k x := by
  induction k with
  | zero => intro x; simp [Q, R, iterS]
  | succ k ih =>
    intro x
    have h := ih (syr x)
    show syr x * Q k (syr x) * x = x * R k (syr x) * iterS k (syr x)
    grind
theorem cycle_identity (K x : Nat) (hx : x % 2 = 1) (hc : iterS K x = x) : 2 ^ V K x * R K x = P K x := by
  have h1 := QR K x
  rw [hc] at h1
  have hQR : Q K x = R K x := Nat.eq_of_mul_eq_mul_right (by omega) h1
  rw [← hQR]; exact prodV K x hx
theorem P_pos (k : Nat) : ∀ x : Nat, 0 < P k x := by
  induction k with
  | zero => intro x; simp [P]
  | succ k ih => intro x; exact Nat.mul_pos (by omega) (ih (syr x))
theorem R_pos (k : Nat) : ∀ x : Nat, x % 2 = 1 → 0 < R k x := by
  induction k with
  | zero => intro x _; simp [R]
  | succ k ih => intro x hx; exact Nat.mul_pos (by omega) (ih (syr x) (syr_spec x hx).2.1)
theorem lower_le (k : Nat) : ∀ x : Nat, 3 ^ k * R k x ≤ P k x := by
  induction k with
  | zero => intro x; simp [R, P]
  | succ k ih =>
    intro x
    have h := ih (syr x)
    show 3 ^ (k + 1) * (x * R k (syr x)) ≤ (3 * x + 1) * P k (syr x)
    have h2 : 3 ^ (k + 1) * (x * R k (syr x)) = (3 * x) * (3 ^ k * R k (syr x)) := by rw [Nat.pow_succ]; grind
    rw [h2]
    exact Nat.mul_le_mul (by omega) h
theorem lower_lt (k x : Nat) : 3 ^ (k + 1) * R (k + 1) x < P (k + 1) x := by
  have h := lower_le k (syr x)
  have hp := P_pos k (syr x)
  show 3 ^ (k + 1) * (x * R k (syr x)) < (3 * x + 1) * P k (syr x)
  have h2 : 3 ^ (k + 1) * (x * R k (syr x)) = (3 * x) * (3 ^ k * R k (syr x)) := by rw [Nat.pow_succ]; grind
  rw [h2]
  calc (3 * x) * (3 ^ k * R k (syr x)) ≤ (3 * x) * P k (syr x) := Nat.mul_le_mul (Nat.le_refl _) h
    _ < (3 * x + 1) * P k (syr x) := by
      have : (3 * x + 1) * P k (syr x) = 3 * x * P k (syr x) + P k (syr x) := by grind
      omega
theorem upper (k : Nat) : ∀ x m : Nat, (∀ i, i < k → m ≤ iterS i x) → P k x * m ^ k ≤ (3 * m + 1) ^ k * R k x := by
  induction k with
  | zero => intro x m _; simp [P, R]
  | succ k ih =>
    intro x m hm
    have h0 : m ≤ x := hm 0 (by omega)
    have hrest : ∀ i, i < k → m ≤ iterS i (syr x) := fun i hi => hm (i + 1) (by omega)
    have h := ih (syr x) m hrest
    show (3 * x + 1) * P k (syr x) * m ^ (k + 1) ≤ (3 * m + 1) ^ (k + 1) * (x * R k (syr x))
    have hx : (3 * x + 1) * m ≤ (3 * m + 1) * x := by
      have : (3 * x + 1) * m = 3 * x * m + m := by grind
      have : (3 * m + 1) * x = 3 * x * m + x := by grind
      omega
    have e1 : (3 * x + 1) * P k (syr x) * m ^ (k + 1) = ((3 * x + 1) * m) * (P k (syr x) * m ^ k) := by
      rw [Nat.pow_succ]; grind
    have e2 : (3 * m + 1) ^ (k + 1) * (x * R k (syr x)) = ((3 * m + 1) * x) * ((3 * m + 1) ^ k * R k (syr x)) := by
      rw [Nat.pow_succ]; grind
    rw [e1, e2]
    exact Nat.mul_le_mul hx h
def minOrb : Nat → Nat → Nat | 0, x => x | k + 1, x => min x (minOrb k (syr x))
theorem minOrb_le (k : Nat) : ∀ x i : Nat, i ≤ k → minOrb k x ≤ iterS i x := by
  induction k with
  | zero => intro x i hi; have : i = 0 := by omega
            subst this; simp [minOrb, iterS]
  | succ k ih =>
    intro x i hi
    cases i with
    | zero => simp [minOrb, iterS]; omega
    | succ i =>
      have := ih (syr x) i (by omega)
      show min x (minOrb k (syr x)) ≤ iterS i (syr x)
      omega
theorem minOrb_mem (k : Nat) : ∀ x : Nat, ∃ i, i ≤ k ∧ iterS i x = minOrb k x := by
  induction k with
  | zero => intro x; exact ⟨0, by omega, by simp [iterS, minOrb]⟩
  | succ k ih =>
    intro x
    obtain ⟨i, hi, he⟩ := ih (syr x)
    by_cases h : x ≤ minOrb k (syr x)
    · exact ⟨0, by omega, by simp [iterS, minOrb]; omega⟩
    · exact ⟨i + 1, by omega, by show iterS i (syr x) = min x (minOrb k (syr x)); rw [he]; omega⟩
-- One Syracuse step with kernel-accelerated operations: p = lowest set bit of 3x + 1, q = (3x + 1) / p.
-- syrOK certifies q * p = 3x + 1, q odd and p | 2^64; coprimality then gives q = syr x.
def lowP (y : Nat) : Nat := Nat.land y (Nat.xor y (Nat.sub y 1))
def syrQ (x : Nat) : Nat := Nat.div (Nat.add (Nat.mul 3 x) 1) (lowP (Nat.add (Nat.mul 3 x) 1))
def syrOK (x : Nat) : Bool := Nat.beq (Nat.mul (syrQ x) (lowP (Nat.add (Nat.mul 3 x) 1))) (Nat.add (Nat.mul 3 x) 1) &&
  Nat.beq (Nat.mod (syrQ x) 2) 1 && Nat.beq (Nat.mod (Nat.pow 2 64) (lowP (Nat.add (Nat.mul 3 x) 1))) 0
theorem odd_cop (q : Nat) (h : q % 2 = 1) : Nat.Coprime q 2 := by
  show Nat.gcd q 2 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec, h]
  decide
theorem syrQ_eq (x : Nat) (hx : x % 2 = 1) (h : syrOK x = true) : syrQ x = syr x := by
  simp only [syrOK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨e1, e2, _⟩ := syr_spec x hx
  have h4 : 2 ^ v x * syr x = syrQ x * lowP (3 * x + 1) := e1.trans h1.symm
  apply Nat.dvd_antisymm
  · exact (Nat.Coprime.pow_right (v x) (odd_cop _ h2)).dvd_of_dvd_mul_left ⟨_, h4⟩
  · have h5 : syr x ∣ syrQ x * 2 ^ 64 :=
      Nat.dvd_trans ⟨2 ^ v x, h4.symm.trans (Nat.mul_comm _ _)⟩ (Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero h3))
    exact (Nat.Coprime.pow_right 64 (odd_cop _ e2)).dvd_of_dvd_mul_right h5
theorem syr_one : syr 1 = 1 := by decide
theorem iterS_one (k : Nat) : iterS k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => show iterS k (syr 1) = 1; rw [syr_one]; exact ih
-- dropsF f t m: within f steps the orbit of m falls below t. Written with Nat.rec (evaluated only by the kernel).
noncomputable def dropsF (f : Nat) : Nat → Nat → Bool :=
  Nat.rec (fun _ _ => false) (fun _ r t m => syrOK m && (Nat.blt (syrQ m) t || r t (syrQ m))) f
theorem dropsF_succ (f t m : Nat) : dropsF (f + 1) t m = (syrOK m && (Nat.blt (syrQ m) t || dropsF f t (syrQ m))) := rfl
theorem dropsF_sound (f : Nat) : ∀ t m : Nat, m % 2 = 1 → dropsF f t m = true → ∃ j, 1 ≤ j ∧ iterS j m < t := by
  induction f with
  | zero => intro t m _ h; cases h
  | succ f ih =>
    intro t m hm h
    rw [dropsF_succ] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
    obtain ⟨hb, h2⟩ := h
    rw [syrQ_eq m hm hb] at h2
    rcases h2 with h2 | h2
    · exact ⟨1, by omega, by simpa [iterS] using h2⟩
    · obtain ⟨j, hj, hl⟩ := ih t (syr m) (syr_spec m hm).2.1 h2
      exact ⟨j + 1, by omega, by simpa [iterS] using hl⟩
-- A Syracuse image is never a multiple of 3: 2^v * syr x = 3x + 1.
theorem syr_mod3 (x : Nat) (hx : x % 2 = 1) : syr x % 3 ≠ 0 := by
  obtain ⟨e1, _, _⟩ := syr_spec x hx
  intro h
  obtain ⟨m, hm⟩ : ∃ m, syr x = 3 * m := ⟨syr x / 3, by omega⟩
  rw [hm, Nat.mul_left_comm] at e1
  omega
theorem iterS_mod3 (j x : Nat) (hx : x % 2 = 1) : iterS (j + 1) x % 3 ≠ 0 := by
  rw [Nat.add_comm, iterS_add]; exact syr_mod3 _ (iterS_odd j x hx)
-- dropRange lo c checks lo + 12j + 7 and lo + 12j + 11 (j < c): the n = 3 (mod 4) that are not multiples of 3.
noncomputable def dropRange (lo : Nat) : Nat → Bool
  | 0 => true
  | c + 1 => dropsF 120 (lo + 12 * c + 7) (lo + 12 * c + 7) && dropsF 120 (lo + 12 * c + 11) (lo + 12 * c + 11) && dropRange lo c
theorem dropRange_sound (lo : Nat) (hl : lo % 12 = 0) : ∀ c n : Nat, dropRange lo c = true → lo ≤ n → n < lo + 12 * c →
    n % 4 = 3 → n % 3 ≠ 0 → ∃ j, 1 ≤ j ∧ iterS j n < n := by
  intro c
  induction c with
  | zero => intro n _ h1 h2; omega
  | succ c ih =>
    intro n h hlo hhi hm h3
    simp only [dropRange, Bool.and_eq_true] at h
    by_cases hn : n = lo + 12 * c + 7
    · subst hn; exact dropsF_sound 120 _ _ (by omega) h.1.1
    · by_cases hn' : n = lo + 12 * c + 11
      · subst hn'; exact dropsF_sound 120 _ _ (by omega) h.1.2
      · exact ih n h.2 hlo (by omega) hm h3
theorem drop_mod4 (n : Nat) (h : n % 4 = 1) (h3 : 3 ≤ n) : ∃ j, 1 ≤ j ∧ iterS j n < n := by
  obtain ⟨e1, e2, e3⟩ := syr_spec n (by omega)
  refine ⟨1, by omega, ?_⟩
  show syr n < n
  by_cases hv : v n = 1
  · rw [hv] at e1; omega
  · have h4 : 2 ^ 2 ≤ 2 ^ v n := Nat.pow_le_pow_right (by decide) (by omega)
    have h5 : 2 ^ 2 * syr n ≤ 2 ^ v n * syr n := Nat.mul_le_mul_right _ h4
    omega

noncomputable def dR (i : Nat) : Bool := dropRange (3900 * i) 325
theorem d0 : dR 0 = true := by decide +kernel theorem d1 : dR 1 = true := by decide +kernel theorem d2 : dR 2 = true := by decide +kernel theorem d3 : dR 3 = true := by decide +kernel theorem d4 : dR 4 = true := by decide +kernel theorem d5 : dR 5 = true := by decide +kernel theorem d6 : dR 6 = true := by decide +kernel theorem d7 : dR 7 = true := by decide +kernel
theorem d8 : dR 8 = true := by decide +kernel theorem d9 : dR 9 = true := by decide +kernel theorem d10 : dR 10 = true := by decide +kernel theorem d11 : dR 11 = true := by decide +kernel theorem d12 : dR 12 = true := by decide +kernel theorem d13 : dR 13 = true := by decide +kernel theorem d14 : dR 14 = true := by decide +kernel theorem d15 : dR 15 = true := by decide +kernel
theorem d16 : dR 16 = true := by decide +kernel theorem d17 : dR 17 = true := by decide +kernel theorem d18 : dR 18 = true := by decide +kernel theorem d19 : dR 19 = true := by decide +kernel theorem d20 : dR 20 = true := by decide +kernel theorem d21 : dR 21 = true := by decide +kernel theorem d22 : dR 22 = true := by decide +kernel theorem d23 : dR 23 = true := by decide +kernel
theorem d24 : dR 24 = true := by decide +kernel theorem d25 : dR 25 = true := by decide +kernel theorem d26 : dR 26 = true := by decide +kernel theorem d27 : dR 27 = true := by decide +kernel theorem d28 : dR 28 = true := by decide +kernel theorem d29 : dR 29 = true := by decide +kernel theorem d30 : dR 30 = true := by decide +kernel theorem d31 : dR 31 = true := by decide +kernel
theorem d32 : dR 32 = true := by decide +kernel theorem d33 : dR 33 = true := by decide +kernel theorem d34 : dR 34 = true := by decide +kernel theorem d35 : dR 35 = true := by decide +kernel theorem d36 : dR 36 = true := by decide +kernel theorem d37 : dR 37 = true := by decide +kernel theorem d38 : dR 38 = true := by decide +kernel theorem d39 : dR 39 = true := by decide +kernel
theorem d40 : dR 40 = true := by decide +kernel theorem d41 : dR 41 = true := by decide +kernel theorem d42 : dR 42 = true := by decide +kernel theorem d43 : dR 43 = true := by decide +kernel theorem d44 : dR 44 = true := by decide +kernel theorem d45 : dR 45 = true := by decide +kernel theorem d46 : dR 46 = true := by decide +kernel theorem d47 : dR 47 = true := by decide +kernel
theorem d48 : dR 48 = true := by decide +kernel theorem d49 : dR 49 = true := by decide +kernel theorem d50 : dR 50 = true := by decide +kernel theorem d51 : dR 51 = true := by decide +kernel theorem d52 : dR 52 = true := by decide +kernel theorem d53 : dR 53 = true := by decide +kernel theorem d54 : dR 54 = true := by decide +kernel theorem d55 : dR 55 = true := by decide +kernel
theorem d56 : dR 56 = true := by decide +kernel theorem d57 : dR 57 = true := by decide +kernel theorem d58 : dR 58 = true := by decide +kernel theorem d59 : dR 59 = true := by decide +kernel theorem d60 : dR 60 = true := by decide +kernel theorem d61 : dR 61 = true := by decide +kernel theorem d62 : dR 62 = true := by decide +kernel theorem d63 : dR 63 = true := by decide +kernel
theorem d64 : dR 64 = true := by decide +kernel theorem d65 : dR 65 = true := by decide +kernel theorem d66 : dR 66 = true := by decide +kernel theorem d67 : dR 67 = true := by decide +kernel theorem d68 : dR 68 = true := by decide +kernel theorem d69 : dR 69 = true := by decide +kernel theorem d70 : dR 70 = true := by decide +kernel theorem d71 : dR 71 = true := by decide +kernel
theorem d72 : dR 72 = true := by decide +kernel theorem d73 : dR 73 = true := by decide +kernel theorem d74 : dR 74 = true := by decide +kernel theorem d75 : dR 75 = true := by decide +kernel theorem d76 : dR 76 = true := by decide +kernel theorem d77 : dR 77 = true := by decide +kernel theorem d78 : dR 78 = true := by decide +kernel theorem d79 : dR 79 = true := by decide +kernel
theorem d80 : dR 80 = true := by decide +kernel theorem d81 : dR 81 = true := by decide +kernel theorem d82 : dR 82 = true := by decide +kernel theorem d83 : dR 83 = true := by decide +kernel theorem d84 : dR 84 = true := by decide +kernel
theorem dUp (k : Nat) (h : ∀ i, i < k → dR i = true) (hk : dR k = true) : ∀ i, i < k + 1 → dR i = true := by
  intro i hi
  by_cases e : i = k
  · subst e; exact hk
  · exact h i (by omega)
theorem dAll : ∀ i, i < 85 → dR i = true :=
  dUp 84 (dUp 83 (dUp 82 (dUp 81 (dUp 80 (dUp 79 (dUp 78 (dUp 77 (dUp 76 (dUp 75 (dUp 74 (dUp 73 (dUp 72 (dUp 71 (dUp 70 (dUp 69 (dUp 68 (dUp 67 (dUp 66 (dUp 65 (dUp 64 (dUp 63 (dUp 62 (dUp 61 (dUp 60 (dUp 59 (dUp 58 (dUp 57 (dUp 56 (dUp 55 (dUp 54 (dUp 53 (dUp 52 (dUp 51 (dUp 50 (dUp 49 (dUp 48 (dUp 47 (dUp 46 (dUp 45 (dUp 44 (dUp 43 (dUp 42 (dUp 41 (dUp 40 (dUp 39 (dUp 38 (dUp 37 (dUp 36 (dUp 35 (dUp 34 (dUp 33 (dUp 32 (dUp 31 (dUp 30 (dUp 29 (dUp 28 (dUp 27 (dUp 26 (dUp 25 (dUp 24 (dUp 23 (dUp 22 (dUp 21 (dUp 20 (dUp 19 (dUp 18 (dUp 17 (dUp 16 (dUp 15 (dUp 14 (dUp 13 (dUp 12 (dUp 11 (dUp 10 (dUp 9 (dUp 8 (dUp 7 (dUp 6 (dUp 5 (dUp 4 (dUp 3 (dUp 2 (dUp 1 (dUp 0 (fun _ h => absurd h (Nat.not_lt_zero _)) d0) d1) d2) d3) d4) d5) d6) d7) d8) d9) d10) d11) d12) d13) d14) d15) d16) d17) d18) d19) d20) d21) d22) d23) d24) d25) d26) d27) d28) d29) d30) d31) d32) d33) d34) d35) d36) d37) d38) d39) d40) d41) d42) d43) d44) d45) d46) d47) d48) d49) d50) d51) d52) d53) d54) d55) d56) d57) d58) d59) d60) d61) d62) d63) d64) d65) d66) d67) d68) d69) d70) d71) d72) d73) d74) d75) d76) d77) d78) d79) d80) d81) d82) d83) d84
theorem drops_all (n : Nat) (hn : n ≤ 330749) (ho : n % 2 = 1) (h3 : 3 ≤ n) (h3' : n % 3 ≠ 0) : ∃ j, 1 ≤ j ∧ iterS j n < n :=
  if hm : n % 4 = 1 then drop_mod4 n hm h3 else
  dropRange_sound (3900 * (n / 3900)) (by omega) 325 n (dAll (n / 3900) (by omega)) (by omega) (by omega) (by omega) h3'
theorem reaches_one (n : Nat) : n ≤ 330749 → n % 2 = 1 → n % 3 ≠ 0 → ∃ j, iterS j n = 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn ho h3
    by_cases h1 : n = 1
    · exact ⟨0, by simp [iterS, h1]⟩
    · obtain ⟨j, hj1, hj⟩ := drops_all n hn ho (by omega) h3
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨i, hi⟩ := ih (iterS (j' + 1) n) hj (by omega) (iterS_odd _ n ho) (iterS_mod3 j' n ho)
      exact ⟨i + (j' + 1), by rw [iterS_add]; exact hi⟩
-- s0 K = floor(K log2 3) + 1 through a 64-bit fixed-point log2 3; bndK certifies 2^(s0 K - 1) <= 3^K,
-- so s0 K is at most every S with 3^K < 2^S, and then checks the minimum bound at S = s0 K.
def s0 (K : Nat) : Nat := K * 29237397617229858719 / 18446744073709551616 + 1
def bndK (K : Nat) : Bool := Nat.ble (2 ^ (s0 K - 1)) (3 ^ K) && Nat.blt ((3 * 330749 + 4) ^ K) (2 ^ s0 K * 330750 ^ K)
def bndRange (lo : Nat) : Nat → Bool | 0 => true | c + 1 => bndK (lo + c) && bndRange lo c
theorem bndRange_sound (lo : Nat) : ∀ c K : Nat, bndRange lo c = true → lo ≤ K → K < lo + c → bndK K = true := by
  intro c; induction c with
  | zero => intro K _ h1 h2; omega
  | succ c ih =>
    intro K h h1 h2
    simp only [bndRange, Bool.and_eq_true] at h
    by_cases e : K = lo + c
    · subst e; exact h.1
    · exact ih K h.2 h1 (by omega)
def bR (i : Nat) : Bool := bndRange (1 + 160 * i) (min 160 (1635 - 160 * i))
theorem b0 : bR 0 = true := by decide +kernel theorem b1 : bR 1 = true := by decide +kernel theorem b2 : bR 2 = true := by decide +kernel theorem b3 : bR 3 = true := by decide +kernel theorem b4 : bR 4 = true := by decide +kernel theorem b5 : bR 5 = true := by decide +kernel theorem b6 : bR 6 = true := by decide +kernel theorem b7 : bR 7 = true := by decide +kernel
theorem b8 : bR 8 = true := by decide +kernel theorem b9 : bR 9 = true := by decide +kernel theorem b10 : bR 10 = true := by decide +kernel
theorem bUp (k : Nat) (h : ∀ i, i < k → bR i = true) (hk : bR k = true) : ∀ i, i < k + 1 → bR i = true := by
  intro i hi
  by_cases e : i = k
  · subst e; exact hk
  · exact h i (by omega)
theorem bAll : ∀ i, i < 11 → bR i = true :=
  bUp 10 (bUp 9 (bUp 8 (bUp 7 (bUp 6 (bUp 5 (bUp 4 (bUp 3 (bUp 2 (bUp 1 (bUp 0 (fun _ h => absurd h (Nat.not_lt_zero _)) b0) b1) b2) b3) b4) b5) b6) b7) b8) b9) b10
theorem bound_fact (K S : Nat) (h1 : 1 ≤ K) (hK : K ≤ 1635) (h3 : 3 ^ K < 2 ^ S) :
    (3 * 330749 + 4) ^ K < 2 ^ S * 330750 ^ K := by
  have hb : bndK K = true :=
    bndRange_sound (1 + 160 * ((K - 1) / 160)) (min 160 (1635 - 160 * ((K - 1) / 160))) K (bAll ((K - 1) / 160) (by omega)) (by omega) (by omega)
  simp only [bndK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
  have h4 : s0 K - 1 < S := (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt hb.1 h3)
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show s0 K ≤ S by omega)
  exact Nat.lt_of_lt_of_le hb.2 (Nat.mul_le_mul_right _ this)
-- Main theorem: every cycle of the Syracuse map with at most 1635 odd elements is the trivial cycle {1}.
-- Equivalently: no Collatz cycle other than 1 -> 4 -> 2 -> 1 contains 1635 or fewer odd terms.
theorem syracuse_cycle_le_1635 (K x : Nat) (hK1 : 1 ≤ K) (hK : K ≤ 1635) (hx : x % 2 = 1)
    (hc : iterS K x = x) : x = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  obtain ⟨i, hi, hiM⟩ := minOrb_mem k x
  have hle : ∀ j, j < k + 1 → minOrb k x ≤ iterS j x := fun j hj => minOrb_le k x j (by omega)
  have hMo : minOrb k x % 2 = 1 := by rw [← hiM]; exact iterS_odd i x hx
  have hid := cycle_identity (k + 1) x hx hc
  have hlow := lower_lt k x
  have hup := upper (k + 1) x (minOrb k x) hle
  have hRpos := R_pos (k + 1) x hx
  have hMp : 0 < minOrb k x ^ (k + 1) := Nat.pow_pos (by omega)
  have h3 : 3 ^ (k + 1) < 2 ^ V (k + 1) x := by
    have : 3 ^ (k + 1) * R (k + 1) x < 2 ^ V (k + 1) x * R (k + 1) x := by rw [hid]; exact hlow
    exact Nat.lt_of_mul_lt_mul_right this
  have hV : 2 ^ V (k + 1) x * minOrb k x ^ (k + 1) ≤ (3 * minOrb k x + 1) ^ (k + 1) := by
    have : 2 ^ V (k + 1) x * minOrb k x ^ (k + 1) * R (k + 1) x ≤ (3 * minOrb k x + 1) ^ (k + 1) * R (k + 1) x := by
      have e : 2 ^ V (k + 1) x * minOrb k x ^ (k + 1) * R (k + 1) x = P (k + 1) x * minOrb k x ^ (k + 1) := by
        rw [← hid]; grind
      rw [e]; exact hup
    exact Nat.le_of_mul_le_mul_right this hRpos
  have hMB : minOrb k x ≤ 330749 := by
    apply Nat.le_of_not_lt; intro hbig
    have hmono : (3 * minOrb k x + 1) * 330750 ≤ (3 * 330749 + 4) * minOrb k x := by omega
    have hpow := Nat.pow_le_pow_left hmono (k + 1)
    rw [Nat.mul_pow, Nat.mul_pow] at hpow
    have htab := bound_fact (k + 1) (V (k + 1) x) (by omega) hK h3
    have c1 := Nat.mul_le_mul_right (330750 ^ (k + 1)) hV
    have c2 := Nat.mul_lt_mul_of_pos_right htab hMp
    have e : 2 ^ V (k + 1) x * minOrb k x ^ (k + 1) * 330750 ^ (k + 1) = 2 ^ V (k + 1) x * 330750 ^ (k + 1) * minOrb k x ^ (k + 1) := by
      rw [Nat.mul_right_comm]
    have := Nat.lt_of_le_of_lt (Nat.le_trans c1 hpow) c2
    rw [e] at this
    exact Nat.lt_irrefl _ this
  have hper : iterS (k + 1) (minOrb k x) = minOrb k x := by
    rw [← hiM, ← iterS_add, Nat.add_comm, iterS_add, hc]
  have hM3 : minOrb k x % 3 ≠ 0 := by
    have h := iterS_mod3 k _ hMo
    rw [hper] at h
    exact h
  obtain ⟨j, hj⟩ := reaches_one (minOrb k x) hMB hMo hM3
  have hpert : ∀ t, iterS ((k + 1) * t) (minOrb k x) = minOrb k x := by
    intro t
    induction t with
    | zero => simp [iterS]
    | succ t ih => rw [Nat.mul_succ, Nat.add_comm, iterS_add, ih, hper]
  have hM1 : minOrb k x = 1 := by
    have h := hpert (j + 1)
    have hj1 : j + 1 ≤ (k + 1) * (j + 1) := Nat.le_mul_of_pos_left (j + 1) (by omega)
    have hsplit : (k + 1) * (j + 1) = ((k + 1) * (j + 1) - j) + j := by omega
    rw [hsplit, iterS_add, hj, iterS_one] at h
    exact h.symm
  have hx1 : iterS (k + 1) x = iterS ((k + 1) - i) (iterS i x) := by
    rw [← iterS_add]; congr 1; omega
  rw [hc, hiM, hM1, iterS_one] at hx1
  exact hx1
#print axioms syracuse_cycle_le_1635
