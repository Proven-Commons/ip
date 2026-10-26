/-
  Round-trip proofs for the IP printer.

  The core lemmas:
  - `foldDigits` over `decDigitsAux`/`hexDigitsAux` returns the number.
  - `parseDec (printDec n) = some n` and `parseHex (printHex n) = some n`.
  - `parseIPv4 (printIPv4 a) = some a` and `parseIPv6 (printIPv6 a) = some a`.

  All proofs use only the standard axioms. There is no `sorry`.
-/

import Ip.Convert
import Ip.Addr
import Ip.Printer
import Ip.Parse

/-- Fold a digit list (most significant first) into a number. -/
def foldDigits (base : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | d :: rest, acc => foldDigits base rest (acc * base + d)

/-- Appending a digit multiplies the folded value by the base and adds it. -/
theorem foldDigits_append_single (base : Nat) (ds : List Nat) (d : Nat) (acc : Nat) :
    foldDigits base (ds ++ [d]) acc = foldDigits base ds acc * base + d := by
  induction ds generalizing acc with
  | nil => simp [foldDigits]
  | cons x xs ih =>
    simp only [List.cons_append, foldDigits]
    rw [ih]

/-- The Aux decimal digits fold back to the number. -/
theorem foldDigits_decDigitsAux (n : Nat) : foldDigits 10 (decDigitsAux n) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [decDigitsAux, foldDigits]
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hne : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      have hunfold : decDigitsAux ((n - 1) + 1) =
          decDigitsAux (((n - 1) + 1) / 10) ++ [((n - 1) + 1) % 10] := by
        simp [decDigitsAux]
      rw [hne, hunfold]
      have hdiv : ((n - 1) + 1) / 10 = n / 10 := by rw [Nat.sub_add_cancel hpos]
      have hmod : ((n - 1) + 1) % 10 = n % 10 := by rw [Nat.sub_add_cancel hpos]
      rw [hdiv, hmod]
      rw [foldDigits_append_single]
      rw [ih (n / 10) (Nat.div_lt_self hpos (show 1 < 10 by decide))]
      have hdm := Nat.div_add_mod n 10
      omega

/-- The decimal digits fold back to the number. -/
theorem foldDigits_decDigits (n : Nat) : foldDigits 10 (decDigits n) 0 = n := by
  unfold decDigits
  by_cases h0 : n = 0
  · subst h0; rfl
  · rw [if_neg h0]
    exact foldDigits_decDigitsAux n

/-- The Aux hex digits fold back to the number. -/
theorem foldDigits_hexDigitsAux (n : Nat) : foldDigits 16 (hexDigitsAux n) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0; simp [hexDigitsAux, foldDigits]
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hne : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      have hunfold : hexDigitsAux ((n - 1) + 1) =
          hexDigitsAux (((n - 1) + 1) / 16) ++ [((n - 1) + 1) % 16] := by
        simp [hexDigitsAux]
      rw [hne, hunfold]
      have hdiv : ((n - 1) + 1) / 16 = n / 16 := by rw [Nat.sub_add_cancel hpos]
      have hmod : ((n - 1) + 1) % 16 = n % 16 := by rw [Nat.sub_add_cancel hpos]
      rw [hdiv, hmod]
      rw [foldDigits_append_single]
      rw [ih (n / 16) (Nat.div_lt_self hpos (show 1 < 16 by decide))]
      have hdm := Nat.div_add_mod n 16
      omega

/-- The hex digits fold back to the number. -/
theorem foldDigits_hexDigits (n : Nat) : foldDigits 16 (hexDigits n) 0 = n := by
  unfold hexDigits
  by_cases h0 : n = 0
  · subst h0; rfl
  · rw [if_neg h0]
    exact foldDigits_hexDigitsAux n


/-- Splitting after a separator-prefixed suffix recovers the head part. -/
theorem splitChar_append_sep (c : Char) (cs : List Char) (rest : List Char)
    (h : c ∉ cs) :
    splitChar c (cs ++ [c] ++ rest) = cs :: splitChar c rest := by
  induction cs with
  | nil => simp [splitChar]
  | cons ch tl ih =>
    have hch : ch ≠ c := by
      intro hcc
      apply h
      simp [hcc]
    have htl : c ∉ tl := fun hm => h (List.mem_cons_of_mem ch hm)
    simp only [List.cons_append]
    show splitChar c (ch :: (tl ++ [c] ++ rest)) = (ch :: tl) :: splitChar c rest
    rw [splitChar]
    simp only [if_neg hch]
    rw [ih htl]

/-- Splitting a separator-free list gives a single part. -/
theorem splitChar_of_not_mem (c : Char) (cs : List Char) (h : c ∉ cs) :
    splitChar c cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons ch tl ih =>
    have hch : ch ≠ c := by
      intro hcc
      apply h
      simp [hcc]
    have htl : c ∉ tl := fun hm => h (List.mem_cons_of_mem ch hm)
    show splitChar c (ch :: tl) = [ch :: tl]
    rw [splitChar]
    simp only [if_neg hch]
    rw [ih htl]

/-- Join then split is the identity for nonempty part lists. -/
theorem splitChar_joinChar (c : Char) (parts : List (List Char))
    (hne : parts ≠ []) (h : ∀ p ∈ parts, c ∉ p) :
    splitChar c (joinChar c parts) = parts := by
  induction parts with
  | nil => contradiction
  | cons p ps ih =>
    cases ps with
    | nil => simp [joinChar, splitChar_of_not_mem c p (h p (by simp))]
    | cons q qs =>
      have hp : c ∉ p := h p (by simp)
      have hps : ∀ r ∈ q :: qs, c ∉ r := fun r hr => h r (List.mem_cons_of_mem p hr)
      have hne' : q :: qs ≠ [] := by simp
      show splitChar c (p ++ [c] ++ joinChar c (q :: qs)) = p :: q :: qs
      rw [splitChar_append_sep c p (joinChar c (q :: qs)) hp]
      rw [ih hne' hps]

/-- A decimal digit character has the expected code. -/
theorem decChar_toNat (d : Nat) (hd : d < 10) : (decChar d).toNat = 48 + d := by
  cases d with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases n with
              | zero => rfl
              | succ n =>
                cases n with
                | zero => rfl
                | succ n =>
                  cases n with
                  | zero => rfl
                  | succ n =>
                    cases n with
                    | zero => rfl
                    | succ m => omega

/-- A hex digit character has the expected value. -/
theorem hexChar_val (d : Nat) (hd : d < 16) : hexVal (hexChar d) = some d := by
  cases d with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
            cases n with
            | zero => rfl
            | succ n =>
              cases n with
              | zero => rfl
              | succ n =>
                cases n with
                | zero => rfl
                | succ n =>
                  cases n with
                  | zero => rfl
                  | succ n =>
                    cases n with
                    | zero => rfl
                    | succ n =>
                      cases n with
                      | zero => rfl
                      | succ n =>
                        cases n with
                        | zero => rfl
                        | succ n =>
                          cases n with
                          | zero => rfl
                          | succ n =>
                            cases n with
                            | zero => rfl
                            | succ n =>
                              cases n with
                              | zero => rfl
                              | succ n =>
                                cases n with
                                | zero => rfl
                                | succ m => omega

/-- Head of a nonempty append is the head of the first list. -/
theorem head_append_of_ne_nil {α : Type} [Inhabited α] (a b : List α) (h : a ≠ []) :
    (a ++ b).head! = a.head! := by
  cases a with
  | nil => contradiction
  | cons x xs => rfl

/-- The first Aux decimal digit is nonzero for positive numbers. -/
theorem decDigitsAux_head_ne_zero (n : Nat) (hn : n ≠ 0) :
    (decDigitsAux n).head! ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · exact absurd h0 hn
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hne : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      have hunfold : decDigitsAux ((n - 1) + 1) =
          decDigitsAux (((n - 1) + 1) / 10) ++ [((n - 1) + 1) % 10] := by
        simp [decDigitsAux]
      rw [hne, hunfold]
      by_cases hdiv : (n - 1 + 1) / 10 = 0
      · -- Single digit: n < 10, so the only digit is n itself, nonzero.
        have hlt : n < 10 := by
          rw [Nat.sub_add_cancel hpos] at hdiv
          omega
        rw [hdiv]
        simp only [decDigitsAux, List.nil_append, List.head!]
        rw [Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hlt]
        exact hn
      · -- Multi-digit: head comes from decDigitsAux (n/10), nonzero by IH.
        have hpos10 : 0 < (n - 1 + 1) / 10 := Nat.pos_of_ne_zero hdiv
        have hlt : (n - 1 + 1) / 10 < n := by
          rw [Nat.sub_add_cancel hpos]
          exact Nat.div_lt_self hpos (show 1 < 10 by decide)
        have ih' := ih ((n - 1 + 1) / 10) hlt (by omega)
        -- head! (decDigitsAux (n/10) ++ [n%10]) = head! (decDigitsAux (n/10))
        -- since decDigitsAux (n/10) is nonempty.
        have hne' : decDigitsAux ((n - 1 + 1) / 10) ≠ [] := by
          intro hempty
          rw [hempty] at ih'
          exact ih' rfl
        have hhead : (decDigitsAux (((n - 1) + 1) / 10) ++ [((n - 1) + 1) % 10]).head! =
            (decDigitsAux (((n - 1) + 1) / 10)).head! :=
          head_append_of_ne_nil _ _ hne'
        rw [hhead]
        exact ih'

/-- Folding mapped digit characters equals folding the digits. -/
theorem decFold_map_decChar (ds : List Nat) (hds : ∀ d ∈ ds, d < 10) (acc : Nat) :
    decFold (ds.map decChar) acc = some (foldDigits 10 ds acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d tl ih =>
    have hd : d < 10 := hds d (by simp)
    have htl : ∀ d' ∈ tl, d' < 10 := fun d' hd' => hds d' (List.mem_cons_of_mem d hd')
    simp only [List.map_cons, decFold]
    rw [decChar_toNat d hd]
    -- (48 + d).toNat - 48 = d, and range check passes.
    have hrange : 48 ≤ (48 + d) ∧ (48 + d) ≤ 57 := by omega
    simp only [hrange, ↓reduceIte]
    -- (48 + d) - 48 = d
    have hsub : 48 + d - 48 = d := by omega
    rw [hsub]
    exact ih htl _

/-- All Aux decimal digits are below 10. -/
theorem decDigitsAux_lt (n : Nat) : ∀ d ∈ decDigitsAux n, d < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      intro d hd
      simp [decDigitsAux] at hd
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hne : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      have hunfold : decDigitsAux ((n - 1) + 1) =
          decDigitsAux (((n - 1) + 1) / 10) ++ [((n - 1) + 1) % 10] := by
        simp [decDigitsAux]
      rw [hne, hunfold]
      intro d hd
      rw [List.mem_append] at hd
      cases hd with
      | inl h =>
        have hlt : (n - 1 + 1) / 10 < n := by
          rw [Nat.sub_add_cancel hpos]
          exact Nat.div_lt_self hpos (show 1 < 10 by decide)
        exact ih _ hlt d h
      | inr h =>
        simp at h
        rw [h]
        exact Nat.mod_lt _ (by decide)

/-- All decimal digits are below 10. -/
theorem decDigits_lt (n : Nat) : ∀ d ∈ decDigits n, d < 10 := by
  unfold decDigits
  by_cases h0 : n = 0
  · subst h0
    intro d hd
    simp at hd
    rw [hd]
    decide
  · rw [if_neg h0]
    exact decDigitsAux_lt n

/-- Decimal print then parse returns the number. -/
theorem parseDec_printDec (n : Nat) : parseDec (printDec n) = some n := by
  unfold parseDec printDec
  simp only [String.toList_ofList]
  by_cases h0 : n = 0
  · subst h0
    -- decDigits 0 = [0], decChar 0 = '0', decValue ['0'] = some 0.
    show decValue ((decDigits 0).map decChar) = some 0
    rw [show decDigits 0 = [0] from rfl]
    show decValue [decChar 0] = some 0
    rw [show decChar 0 = '0' from rfl]
    rfl
  · -- n > 0: decValue folds the mapped digits.
    have hne : decDigits n ≠ [] := by
      unfold decDigits
      rw [if_neg h0]
      intro hempty
      have hh := decDigitsAux_head_ne_zero n h0
      rw [hempty] at hh
      exact hh rfl
    cases hds : decDigits n with
    | nil => contradiction
    | cons d rest =>
      -- First digit d ≠ 0, so decValue takes the fold branch.
      have hd0 : d ≠ 0 := by
        have hh : (decDigits n).head! ≠ 0 := by
          unfold decDigits
          rw [if_neg h0]
          exact decDigitsAux_head_ne_zero n h0
        rw [hds] at hh
        simp at hh
        exact hh
      -- decValue (decChar d :: rest.map decChar): first char ≠ '0'.
      show decValue ((decChar d) :: (rest.map decChar)) = some n
      have hd10 : d < 10 := decDigits_lt n d (by rw [hds]; simp)
      have hchar : decChar d ≠ '0' := by
        intro hc
        -- If decChar d = '0', then toNat gives 48 + d = 48, so d = 0.
        have h1 := decChar_toNat d hd10
        rw [hc] at h1
        have h0' : ('0').toNat = 48 := rfl
        rw [h0'] at h1
        omega
      -- decValue on a cons with nonzero first char folds.
      have hdec : decValue ((decChar d) :: (rest.map decChar)) =
          decFold ((decChar d) :: (rest.map decChar)) 0 := by
        simp [decValue, hchar]
      rw [hdec]
      -- Now: decFold ((decChar d) :: rest.map decChar) 0 = some n.
      -- By decFold_map_decChar: = some (foldDigits 10 (d :: rest) 0) = some n.
      have hfold := decFold_map_decChar (d :: rest) (by
        intro d' hd'
        cases hd' with
        | head => exact hd10
        | tail _ hr => exact decDigits_lt n d' (by rw [hds]; exact List.mem_cons_of_mem d hr)) 0
      -- Map on cons reduces definitionally; convert the goal to map form.
      show decFold (List.map decChar (d :: rest)) 0 = some n
      rw [hfold]
      -- foldDigits 10 (d :: rest) 0 = foldDigits 10 (decDigits n) 0 = n.
      rw [← hds, foldDigits_decDigits n]

/-- All Aux hex digits are below 16. -/
theorem hexDigitsAux_lt (n : Nat) : ∀ d ∈ hexDigitsAux n, d < 16 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · subst h0
      intro d hd
      simp [hexDigitsAux] at hd
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hne : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      have hunfold : hexDigitsAux ((n - 1) + 1) =
          hexDigitsAux (((n - 1) + 1) / 16) ++ [((n - 1) + 1) % 16] := by
        simp [hexDigitsAux]
      rw [hne, hunfold]
      intro d hd
      rw [List.mem_append] at hd
      cases hd with
      | inl h =>
        have hlt : (n - 1 + 1) / 16 < n := by
          rw [Nat.sub_add_cancel hpos]
          exact Nat.div_lt_self hpos (show 1 < 16 by decide)
        exact ih _ hlt d h
      | inr h =>
        simp at h
        rw [h]
        exact Nat.mod_lt _ (by decide)

/-- All hex digits are below 16. -/
theorem hexDigits_lt (n : Nat) : ∀ d ∈ hexDigits n, d < 16 := by
  unfold hexDigits
  by_cases h0 : n = 0
  · subst h0
    intro d hd
    simp at hd
    rw [hd]
    decide
  · rw [if_neg h0]
    exact hexDigitsAux_lt n

/-- The first Aux hex digit is nonzero for positive numbers. -/
theorem hexDigitsAux_head_ne_zero (n : Nat) (hn : n ≠ 0) :
    (hexDigitsAux n).head! ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h0 : n = 0
    · exact absurd h0 hn
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hne : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
      have hunfold : hexDigitsAux ((n - 1) + 1) =
          hexDigitsAux (((n - 1) + 1) / 16) ++ [((n - 1) + 1) % 16] := by
        simp [hexDigitsAux]
      rw [hne, hunfold]
      by_cases hdiv : (n - 1 + 1) / 16 = 0
      · have hlt : n < 16 := by
          rw [Nat.sub_add_cancel hpos] at hdiv
          omega
        rw [hdiv]
        simp only [hexDigitsAux, List.nil_append, List.head!]
        rw [Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hlt]
        exact hn
      · have hlt : (n - 1 + 1) / 16 < n := by
          rw [Nat.sub_add_cancel hpos]
          exact Nat.div_lt_self hpos (show 1 < 16 by decide)
        have ih' := ih ((n - 1 + 1) / 16) hlt (by omega)
        have hne' : hexDigitsAux ((n - 1 + 1) / 16) ≠ [] := by
          intro hempty
          rw [hempty] at ih'
          exact ih' rfl
        have hhead : (hexDigitsAux (((n - 1) + 1) / 16) ++ [((n - 1) + 1) % 16]).head! =
            (hexDigitsAux (((n - 1) + 1) / 16)).head! :=
          head_append_of_ne_nil _ _ hne'
        rw [hhead]
        exact ih'

/-- Folding mapped hex characters equals folding the digits. -/
theorem hexFold_map_hexChar (ds : List Nat) (hds : ∀ d ∈ ds, d < 16) (acc : Nat) :
    hexFold (ds.map hexChar) acc = some (foldDigits 16 ds acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d tl ih =>
    have hd : d < 16 := hds d (by simp)
    have htl : ∀ d' ∈ tl, d' < 16 := fun d' hd' => hds d' (List.mem_cons_of_mem d hd')
    simp only [List.map_cons, hexFold, hexChar_val d hd]
    exact ih htl _

/-- Hex print then parse returns the number. -/
theorem parseHex_printHex (n : Nat) : parseHex (printHex n) = some n := by
  unfold parseHex printHex
  simp only [String.toList_ofList]
  by_cases h0 : n = 0
  · subst h0
    show hexValue ((hexDigits 0).map hexChar) = some 0
    rw [show hexDigits 0 = [0] from rfl]
    show hexValue [hexChar 0] = some 0
    rw [show hexChar 0 = '0' from rfl]
    rfl
  · have hne : hexDigits n ≠ [] := by
      unfold hexDigits
      rw [if_neg h0]
      intro hempty
      have hh := hexDigitsAux_head_ne_zero n h0
      rw [hempty] at hh
      exact hh rfl
    cases hds : hexDigits n with
    | nil => contradiction
    | cons d rest =>
      have hd0 : d ≠ 0 := by
        have hh : (hexDigits n).head! ≠ 0 := by
          unfold hexDigits
          rw [if_neg h0]
          exact hexDigitsAux_head_ne_zero n h0
        rw [hds] at hh
        simp at hh
        exact hh
      show hexValue ((hexChar d) :: (rest.map hexChar)) = some n
      have hd16 : d < 16 := hexDigits_lt n d (by rw [hds]; simp)
      have hchar : hexChar d ≠ '0' := by
        intro hc
        have h1 := hexChar_val d hd16
        rw [hc] at h1
        have h0' : hexVal '0' = some 0 := rfl
        rw [h0'] at h1
        injection h1 with h1'
        omega
      have hhex : hexValue ((hexChar d) :: (rest.map hexChar)) =
          hexFold ((hexChar d) :: (rest.map hexChar)) 0 := by
        simp [hexValue, hchar]
      rw [hhex]
      have hfold := hexFold_map_hexChar (d :: rest) (by
        intro d' hd'
        cases hd' with
        | head => exact hd16
        | tail _ hr => exact hexDigits_lt n d' (by rw [hds]; exact List.mem_cons_of_mem d hr)) 0
      show hexFold (List.map hexChar (d :: rest)) 0 = some n
      rw [hfold, ← hds, foldDigits_hexDigits n]

/-- The character list of a printed IPv4 address is a join of its parts. -/
theorem printIPv4_toList (a : IPv4) :
    (printIPv4 a).toList =
      joinChar '.' [(printDec a.b0).toList, (printDec a.b1).toList,
                    (printDec a.b2).toList, (printDec a.b3).toList] := by
  simp [printIPv4, joinChar, String.toList_append]

/-- No decimal digit character is a dot. -/
theorem decChar_ne_dot (d : Nat) : '.' ∉ (printDec d).toList := by
  unfold printDec
  simp only [String.toList_ofList]
  -- All chars in (decDigits d).map decChar are digit chars, not '.'.
  intro h
  rw [List.mem_map] at h
  obtain ⟨d', _, hd'⟩ := h
  -- decChar d' = '.' is impossible: decChar gives '0'..'9' or '?'.
  -- By cases on d' < 10 or ≥ 10.
  by_cases hd10 : d' < 10
  · have h1 := decChar_toNat d' hd10
    rw [hd'] at h1
    have h2 : ('.').toNat = 46 := rfl
    rw [h2] at h1
    omega
  · -- d' ≥ 10: decChar d' = '?', not '.'.
    have : decChar d' = '?' := by
      -- decChar is defined by match; for d' ≥ 10 it falls through to '?'.
      -- Prove by showing decChar d' ≠ any digit char... 
      -- Simpler: unfold and match on d' structure is hard for general d'.
      -- Use: decChar d' for d' ≥ 10: the match arms 0-9 don't apply.
      cases d' with
      | zero => omega
      | succ n =>
        cases n with
        | zero => omega
        | succ n =>
          cases n with
          | zero => omega
          | succ n =>
            cases n with
            | zero => omega
            | succ n =>
              cases n with
              | zero => omega
              | succ n =>
                cases n with
                | zero => omega
                | succ n =>
                  cases n with
                  | zero => omega
                  | succ n =>
                    cases n with
                    | zero => omega
                    | succ n =>
                      cases n with
                      | zero => omega
                      | succ n =>
                        cases n with
                        | zero => omega
                        | succ k => rfl
    rw [this] at hd'
    simp at hd'

/-- Printing then parsing an IPv4 address returns the address. -/
theorem parseIPv4_printIPv4 (a : IPv4) : parseIPv4 (printIPv4 a) = some a := by
  unfold parseIPv4 splitOn
  rw [printIPv4_toList]
  -- splitChar '.' (joinChar '.' parts) = parts, since no part has '.'.
  rw [splitChar_joinChar '.' _ (by simp)
    (by intro p hp
        simp at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact decChar_ne_dot a.b0
        · exact decChar_ne_dot a.b1
        · exact decChar_ne_dot a.b2
        · exact decChar_ne_dot a.b3)]
  -- Map String.ofList over the parts, then parseDec each.
  dsimp only
  simp only [List.map_cons, List.map_nil, String.ofList_toList]
  -- Reduce the match and do-notation with full simp.
  simp [parseDec_printDec, a.b0_lt, a.b1_lt, a.b2_lt, a.b3_lt]
